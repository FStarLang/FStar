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
              | (embedded_state,uu____59)::[] ->
                  let uu____76 =
                    FStar_Tactics_Embedding.unembed_proofstate embedded_state in
                  FStar_Util.bind_opt uu____76
                    (fun ps  ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                       FStar_Tactics_Basic.log ps1
                         (fun uu____90  ->
                            let uu____91 = FStar_Ident.string_of_lid nm in
                            let uu____92 =
                              FStar_Syntax_Print.args_to_string args in
                            FStar_Util.print2 "Reached %s, args are: %s\n"
                              uu____91 uu____92);
                       (let res = FStar_Tactics_Basic.run t ps1 in
                        let uu____96 =
                          let uu____97 =
                            FStar_TypeChecker_Normalize.psc_range psc in
                          FStar_Tactics_Embedding.embed_result embed_r t_r
                            uu____97 res in
                        FStar_Pervasives_Native.Some uu____96))
              | uu____104 ->
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
                | (a,uu____176)::(embedded_state,uu____178)::[] ->
                    let uu____205 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    FStar_Util.bind_opt uu____205
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____218  ->
                              let uu____219 = FStar_Ident.string_of_lid nm in
                              let uu____220 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____219 uu____220);
                         (let uu____221 = unembed_a a in
                          FStar_Util.bind_opt uu____221
                            (fun a1  ->
                               let res =
                                 let uu____233 = t a1 in
                                 FStar_Tactics_Basic.run uu____233 ps1 in
                               let uu____236 =
                                 let uu____237 =
                                   FStar_TypeChecker_Normalize.psc_range psc in
                                 FStar_Tactics_Embedding.embed_result embed_r
                                   t_r uu____237 res in
                               FStar_Pervasives_Native.Some uu____236)))
                | uu____244 ->
                    let uu____245 =
                      let uu____246 = FStar_Ident.string_of_lid nm in
                      let uu____247 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____246 uu____247 in
                    failwith uu____245
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
                | (a,uu____324)::(embedded_state,uu____326)::[] ->
                    let uu____353 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    FStar_Util.bind_opt uu____353
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____366  ->
                              let uu____367 = FStar_Ident.string_of_lid nm in
                              let uu____368 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____367 uu____368);
                         (let uu____369 = unembed_a a in
                          FStar_Util.bind_opt uu____369
                            (fun a1  ->
                               let res =
                                 let uu____381 = t psc a1 in
                                 FStar_Tactics_Basic.run uu____381 ps1 in
                               let uu____384 =
                                 let uu____385 =
                                   FStar_TypeChecker_Normalize.psc_range psc in
                                 FStar_Tactics_Embedding.embed_result embed_r
                                   t_r uu____385 res in
                               FStar_Pervasives_Native.Some uu____384)))
                | uu____392 ->
                    let uu____393 =
                      let uu____394 = FStar_Ident.string_of_lid nm in
                      let uu____395 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____394 uu____395 in
                    failwith uu____393
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
                  | (a,uu____487)::(b,uu____489)::(embedded_state,uu____491)::[]
                      ->
                      let uu____528 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state in
                      FStar_Util.bind_opt uu____528
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____541  ->
                                let uu____542 = FStar_Ident.string_of_lid nm in
                                let uu____543 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____542
                                  uu____543);
                           (let uu____544 = unembed_a a in
                            FStar_Util.bind_opt uu____544
                              (fun a1  ->
                                 let uu____552 = unembed_b b in
                                 FStar_Util.bind_opt uu____552
                                   (fun b1  ->
                                      let res =
                                        let uu____564 = t a1 b1 in
                                        FStar_Tactics_Basic.run uu____564 ps1 in
                                      let uu____567 =
                                        let uu____568 =
                                          FStar_TypeChecker_Normalize.psc_range
                                            psc in
                                        FStar_Tactics_Embedding.embed_result
                                          embed_r t_r uu____568 res in
                                      FStar_Pervasives_Native.Some uu____567))))
                  | uu____575 ->
                      let uu____576 =
                        let uu____577 = FStar_Ident.string_of_lid nm in
                        let uu____578 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____577 uu____578 in
                      failwith uu____576
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
                    | (a,uu____690)::(b,uu____692)::(c,uu____694)::(embedded_state,uu____696)::[]
                        ->
                        let uu____743 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state in
                        FStar_Util.bind_opt uu____743
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____756  ->
                                  let uu____757 =
                                    FStar_Ident.string_of_lid nm in
                                  let uu____758 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____757
                                    uu____758);
                             (let uu____759 = unembed_a a in
                              FStar_Util.bind_opt uu____759
                                (fun a1  ->
                                   let uu____767 = unembed_b b in
                                   FStar_Util.bind_opt uu____767
                                     (fun b1  ->
                                        let uu____775 = unembed_c c in
                                        FStar_Util.bind_opt uu____775
                                          (fun c1  ->
                                             let res =
                                               let uu____787 = t a1 b1 c1 in
                                               FStar_Tactics_Basic.run
                                                 uu____787 ps1 in
                                             let uu____790 =
                                               let uu____791 =
                                                 FStar_TypeChecker_Normalize.psc_range
                                                   psc in
                                               FStar_Tactics_Embedding.embed_result
                                                 embed_r t_r uu____791 res in
                                             FStar_Pervasives_Native.Some
                                               uu____790)))))
                    | uu____798 ->
                        let uu____799 =
                          let uu____800 = FStar_Ident.string_of_lid nm in
                          let uu____801 =
                            FStar_Syntax_Print.args_to_string args in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____800 uu____801 in
                        failwith uu____799
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
                        | (a,uu____953)::(b,uu____955)::(c,uu____957)::
                            (d,uu____959)::(e,uu____961)::(embedded_state,uu____963)::[]
                            ->
                            let uu____1030 =
                              FStar_Tactics_Embedding.unembed_proofstate
                                embedded_state in
                            FStar_Util.bind_opt uu____1030
                              (fun ps  ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps in
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1043  ->
                                      let uu____1044 =
                                        FStar_Ident.string_of_lid nm in
                                      let uu____1045 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1044 uu____1045);
                                 (let uu____1046 = unembed_a a in
                                  FStar_Util.bind_opt uu____1046
                                    (fun a1  ->
                                       let uu____1054 = unembed_b b in
                                       FStar_Util.bind_opt uu____1054
                                         (fun b1  ->
                                            let uu____1062 = unembed_c c in
                                            FStar_Util.bind_opt uu____1062
                                              (fun c1  ->
                                                 let uu____1070 = unembed_d d in
                                                 FStar_Util.bind_opt
                                                   uu____1070
                                                   (fun d1  ->
                                                      let uu____1078 =
                                                        unembed_e e in
                                                      FStar_Util.bind_opt
                                                        uu____1078
                                                        (fun e1  ->
                                                           let res =
                                                             let uu____1090 =
                                                               t a1 b1 c1 d1
                                                                 e1 in
                                                             FStar_Tactics_Basic.run
                                                               uu____1090 ps1 in
                                                           let uu____1093 =
                                                             let uu____1094 =
                                                               FStar_TypeChecker_Normalize.psc_range
                                                                 psc in
                                                             FStar_Tactics_Embedding.embed_result
                                                               embed_r t_r
                                                               uu____1094 res in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1093)))))))
                        | uu____1101 ->
                            let uu____1102 =
                              let uu____1103 = FStar_Ident.string_of_lid nm in
                              let uu____1104 =
                                FStar_Syntax_Print.args_to_string args in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1103 uu____1104 in
                            failwith uu____1102
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
  fun uu____1156  ->
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
      | (ps,uu____1690)::[] ->
          let uu____1707 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1707
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               let uu____1715 =
                 let uu____1716 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____1717 = FStar_Tactics_Types.decr_depth ps2 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1716
                   uu____1717 in
               FStar_Pervasives_Native.Some uu____1715)
      | uu____1718 -> failwith "Unexpected application of decr_depth" in
    let decr_depth_step =
      let uu____1722 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1722;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      } in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____1735)::[] ->
          let uu____1752 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1752
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               let uu____1760 =
                 let uu____1761 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____1762 = FStar_Tactics_Types.incr_depth ps2 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1761
                   uu____1762 in
               FStar_Pervasives_Native.Some uu____1760)
      | uu____1763 -> failwith "Unexpected application of incr_depth" in
    let incr_depth_step =
      let uu____1767 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1767;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      } in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____1784)::[] ->
          let uu____1801 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1801
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1814 -> failwith "Unexpected application of tracepoint" in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____1831)::(r,uu____1833)::[] ->
          let uu____1860 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1860
            (fun ps1  ->
               let uu____1866 = FStar_Syntax_Embeddings.unembed_range r in
               FStar_Util.bind_opt uu____1866
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1 in
                    let uu____1874 =
                      let uu____1875 =
                        FStar_TypeChecker_Normalize.psc_range psc in
                      FStar_Tactics_Embedding.embed_proofstate uu____1875 ps' in
                    FStar_Pervasives_Native.Some uu____1874))
      | uu____1876 ->
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
      let uu___286_1890 = t in
      {
        FStar_Syntax_Syntax.n = (uu___286_1890.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___286_1890.FStar_Syntax_Syntax.vars)
      } in
    let get1 t = FStar_Pervasives_Native.Some t in
    let uu____1897 =
      let uu____1900 =
        mktac2 "__fail" (fun uu____1902  -> FStar_Tactics_Basic.fail) get1
          FStar_Syntax_Embeddings.unembed_string put1
          FStar_Syntax_Syntax.t_unit in
      let uu____1903 =
        let uu____1906 =
          mktac0 "__trivial" FStar_Tactics_Basic.trivial
            FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit in
        let uu____1907 =
          let uu____1910 =
            let uu____1911 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit in
            mktac2 "__trytac" (fun uu____1921  -> FStar_Tactics_Basic.trytac)
              get1 (unembed_tactic_0' get1) uu____1911
              FStar_Syntax_Syntax.t_unit in
          let uu____1928 =
            let uu____1931 =
              mktac0 "__intro" FStar_Tactics_Basic.intro
                FStar_Reflection_Basic.embed_binder
                FStar_Reflection_Data.fstar_refl_binder in
            let uu____1932 =
              let uu____1935 =
                let uu____1936 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder in
                let uu____1943 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder in
                mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec uu____1936
                  uu____1943 in
              let uu____1954 =
                let uu____1957 =
                  let uu____1958 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step in
                  mktac1 "__norm" FStar_Tactics_Basic.norm uu____1958
                    FStar_Syntax_Embeddings.embed_unit
                    FStar_Syntax_Syntax.t_unit in
                let uu____1969 =
                  let uu____1972 =
                    let uu____1973 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step in
                    mktac3 "__norm_term_env"
                      FStar_Tactics_Basic.norm_term_env
                      FStar_Reflection_Basic.unembed_env uu____1973
                      FStar_Reflection_Basic.unembed_term
                      FStar_Reflection_Basic.embed_term
                      FStar_Syntax_Syntax.t_term in
                  let uu____1984 =
                    let uu____1987 =
                      let uu____1988 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step in
                      mktac2 "__norm_binder_type"
                        FStar_Tactics_Basic.norm_binder_type uu____1988
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Syntax_Embeddings.embed_unit
                        FStar_Syntax_Syntax.t_unit in
                    let uu____1999 =
                      let uu____2002 =
                        mktac2 "__rename_to" FStar_Tactics_Basic.rename_to
                          FStar_Reflection_Basic.unembed_binder
                          FStar_Syntax_Embeddings.unembed_string
                          FStar_Syntax_Embeddings.embed_unit
                          FStar_Syntax_Syntax.t_unit in
                      let uu____2003 =
                        let uu____2006 =
                          mktac1 "__binder_retype"
                            FStar_Tactics_Basic.binder_retype
                            FStar_Reflection_Basic.unembed_binder
                            FStar_Syntax_Embeddings.embed_unit
                            FStar_Syntax_Syntax.t_unit in
                        let uu____2007 =
                          let uu____2010 =
                            mktac0 "__revert" FStar_Tactics_Basic.revert
                              FStar_Syntax_Embeddings.embed_unit
                              FStar_Syntax_Syntax.t_unit in
                          let uu____2011 =
                            let uu____2014 =
                              mktac0 "__clear_top"
                                FStar_Tactics_Basic.clear_top
                                FStar_Syntax_Embeddings.embed_unit
                                FStar_Syntax_Syntax.t_unit in
                            let uu____2015 =
                              let uu____2018 =
                                mktac1 "__clear" FStar_Tactics_Basic.clear
                                  FStar_Reflection_Basic.unembed_binder
                                  FStar_Syntax_Embeddings.embed_unit
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____2019 =
                                let uu____2022 =
                                  mktac1 "__rewrite"
                                    FStar_Tactics_Basic.rewrite
                                    FStar_Reflection_Basic.unembed_binder
                                    FStar_Syntax_Embeddings.embed_unit
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____2023 =
                                  let uu____2026 =
                                    mktac0 "__smt" FStar_Tactics_Basic.smt
                                      FStar_Syntax_Embeddings.embed_unit
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____2027 =
                                    let uu____2030 =
                                      mktac0 "__refine_intro"
                                        FStar_Tactics_Basic.refine_intro
                                        FStar_Syntax_Embeddings.embed_unit
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____2031 =
                                      let uu____2034 =
                                        mktac3 "__t_exact"
                                          FStar_Tactics_Basic.t_exact
                                          FStar_Syntax_Embeddings.unembed_bool
                                          FStar_Syntax_Embeddings.unembed_bool
                                          FStar_Reflection_Basic.unembed_term
                                          FStar_Syntax_Embeddings.embed_unit
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____2035 =
                                        let uu____2038 =
                                          mktac1 "__apply"
                                            (FStar_Tactics_Basic.apply true)
                                            FStar_Reflection_Basic.unembed_term
                                            FStar_Syntax_Embeddings.embed_unit
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____2039 =
                                          let uu____2042 =
                                            mktac1 "__apply_raw"
                                              (FStar_Tactics_Basic.apply
                                                 false)
                                              FStar_Reflection_Basic.unembed_term
                                              FStar_Syntax_Embeddings.embed_unit
                                              FStar_Syntax_Syntax.t_unit in
                                          let uu____2043 =
                                            let uu____2046 =
                                              mktac1 "__apply_lemma"
                                                FStar_Tactics_Basic.apply_lemma
                                                FStar_Reflection_Basic.unembed_term
                                                FStar_Syntax_Embeddings.embed_unit
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____2047 =
                                              let uu____2050 =
                                                let uu____2051 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit in
                                                mktac5 "__divide"
                                                  (fun uu____2068  ->
                                                     fun uu____2069  ->
                                                       FStar_Tactics_Basic.divide)
                                                  get1 get1
                                                  FStar_Syntax_Embeddings.unembed_int
                                                  (unembed_tactic_0' get1)
                                                  (unembed_tactic_0' get1)
                                                  uu____2051
                                                  FStar_Syntax_Syntax.t_unit in
                                              let uu____2076 =
                                                let uu____2079 =
                                                  mktac1 "__set_options"
                                                    FStar_Tactics_Basic.set_options
                                                    FStar_Syntax_Embeddings.unembed_string
                                                    FStar_Syntax_Embeddings.embed_unit
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____2080 =
                                                  let uu____2083 =
                                                    mktac2 "__seq"
                                                      FStar_Tactics_Basic.seq
                                                      (unembed_tactic_0'
                                                         FStar_Syntax_Embeddings.unembed_unit)
                                                      (unembed_tactic_0'
                                                         FStar_Syntax_Embeddings.unembed_unit)
                                                      FStar_Syntax_Embeddings.embed_unit
                                                      FStar_Syntax_Syntax.t_unit in
                                                  let uu____2088 =
                                                    let uu____2091 =
                                                      mktac1 "__tc"
                                                        FStar_Tactics_Basic.tc
                                                        FStar_Reflection_Basic.unembed_term
                                                        FStar_Reflection_Basic.embed_term
                                                        FStar_Syntax_Syntax.t_term in
                                                    let uu____2092 =
                                                      let uu____2095 =
                                                        mktac1 "__unshelve"
                                                          FStar_Tactics_Basic.unshelve
                                                          FStar_Reflection_Basic.unembed_term
                                                          FStar_Syntax_Embeddings.embed_unit
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____2096 =
                                                        let uu____2099 =
                                                          mktac2 "__unquote"
                                                            FStar_Tactics_Basic.unquote
                                                            get1
                                                            FStar_Reflection_Basic.unembed_term
                                                            put1
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____2100 =
                                                          let uu____2103 =
                                                            mktac1 "__prune"
                                                              FStar_Tactics_Basic.prune
                                                              FStar_Syntax_Embeddings.unembed_string
                                                              FStar_Syntax_Embeddings.embed_unit
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____2104 =
                                                            let uu____2107 =
                                                              mktac1
                                                                "__addns"
                                                                FStar_Tactics_Basic.addns
                                                                FStar_Syntax_Embeddings.unembed_string
                                                                FStar_Syntax_Embeddings.embed_unit
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____2108 =
                                                              let uu____2111
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
                                                              let uu____2116
                                                                =
                                                                let uu____2119
                                                                  =
                                                                  mktac1
                                                                    "__dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____2120
                                                                  =
                                                                  let uu____2123
                                                                    =
                                                                    mktac1
                                                                    "__dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____2124
                                                                    =
                                                                    let uu____2127
                                                                    =
                                                                    mktac2
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.unembed_direction
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2130
                                                                    =
                                                                    let uu____2133
                                                                    =
                                                                    mktac0
                                                                    "__trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2134
                                                                    =
                                                                    let uu____2137
                                                                    =
                                                                    mktac0
                                                                    "__later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2138
                                                                    =
                                                                    let uu____2141
                                                                    =
                                                                    mktac0
                                                                    "__dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2142
                                                                    =
                                                                    let uu____2145
                                                                    =
                                                                    mktac0
                                                                    "__flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2146
                                                                    =
                                                                    let uu____2149
                                                                    =
                                                                    mktac0
                                                                    "__qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2150
                                                                    =
                                                                    let uu____2153
                                                                    =
                                                                    let uu____2154
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2161
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    mktac1
                                                                    "__cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    uu____2154
                                                                    uu____2161 in
                                                                    let uu____2172
                                                                    =
                                                                    let uu____2175
                                                                    =
                                                                    mktac0
                                                                    "__top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2176
                                                                    =
                                                                    let uu____2179
                                                                    =
                                                                    mktac0
                                                                    "__cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2180
                                                                    =
                                                                    let uu____2183
                                                                    =
                                                                    mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2184
                                                                    =
                                                                    let uu____2187
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2188
                                                                    =
                                                                    let uu____2191
                                                                    =
                                                                    mktac0
                                                                    "__is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____2192
                                                                    =
                                                                    let uu____2195
                                                                    =
                                                                    let uu____2196
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term in
                                                                    mktac2
                                                                    "__uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Basic.unembed_env
                                                                    uu____2196
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2207
                                                                    =
                                                                    let uu____2210
                                                                    =
                                                                    mktac2
                                                                    "__unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____2211
                                                                    =
                                                                    let uu____2214
                                                                    =
                                                                    mktac3
                                                                    "__launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_string
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____2214;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step] in
                                                                    uu____2210
                                                                    ::
                                                                    uu____2211 in
                                                                    uu____2195
                                                                    ::
                                                                    uu____2207 in
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
                                                                    uu____2175
                                                                    ::
                                                                    uu____2176 in
                                                                    uu____2153
                                                                    ::
                                                                    uu____2172 in
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
                                                                    uu____2133
                                                                    ::
                                                                    uu____2134 in
                                                                    uu____2127
                                                                    ::
                                                                    uu____2130 in
                                                                  uu____2123
                                                                    ::
                                                                    uu____2124 in
                                                                uu____2119 ::
                                                                  uu____2120 in
                                                              uu____2111 ::
                                                                uu____2116 in
                                                            uu____2107 ::
                                                              uu____2108 in
                                                          uu____2103 ::
                                                            uu____2104 in
                                                        uu____2099 ::
                                                          uu____2100 in
                                                      uu____2095 ::
                                                        uu____2096 in
                                                    uu____2091 :: uu____2092 in
                                                  uu____2083 :: uu____2088 in
                                                uu____2079 :: uu____2080 in
                                              uu____2050 :: uu____2076 in
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
                      uu____2002 :: uu____2003 in
                    uu____1987 :: uu____1999 in
                  uu____1972 :: uu____1984 in
                uu____1957 :: uu____1969 in
              uu____1935 :: uu____1954 in
            uu____1931 :: uu____1932 in
          uu____1910 :: uu____1928 in
        uu____1906 :: uu____1907 in
      uu____1900 :: uu____1903 in
    FStar_List.append uu____1897
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
             let uu____2237 =
               let uu____2238 =
                 let uu____2239 =
                   let uu____2240 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state in
                   FStar_Syntax_Syntax.as_arg uu____2240 in
                 [uu____2239] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2238 in
             uu____2237 FStar_Pervasives_Native.None rng in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           (let uu____2247 = FStar_ST.op_Bang tacdbg in
            if uu____2247
            then
              let uu____2296 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2296
            else ());
           (let result =
              let uu____2299 = primitive_steps () in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2299 steps proof_state.FStar_Tactics_Types.main_context
                tm in
            (let uu____2303 = FStar_ST.op_Bang tacdbg in
             if uu____2303
             then
               let uu____2352 = FStar_Syntax_Print.term_to_string result in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2352
             else ());
            (let uu____2354 =
               FStar_Tactics_Embedding.unembed_result result unembed_b in
             match uu____2354 with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2397 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2397
                   (fun uu____2401  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2424 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2424
                   (fun uu____2428  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2441 =
                   let uu____2442 =
                     let uu____2447 =
                       let uu____2448 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____2448 in
                     (uu____2447,
                       ((proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)) in
                   FStar_Errors.Error uu____2442 in
                 FStar_Exn.raise uu____2441)))
and unembed_tactic_0':
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2457 = unembed_tactic_0 unembed_b embedded_tac_b in
      FStar_All.pipe_left (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
        uu____2457
let report_implicits:
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2509  ->
             match uu____2509 with
             | (r,uu____2527,uv,uu____2529,ty,rng) ->
                 let uu____2532 =
                   let uu____2533 = FStar_Syntax_Print.uvar_to_string uv in
                   let uu____2534 = FStar_Syntax_Print.term_to_string ty in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2533 uu____2534 r in
                 (uu____2532, rng)) is in
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
        (let uu____2579 = FStar_ST.op_Bang tacdbg in
         if uu____2579
         then
           let uu____2628 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2628
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         FStar_Errors.stop_if_err ();
         (let tau =
            unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic1 in
          let uu____2635 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____2635 with
          | (env1,uu____2649) ->
              let env2 =
                let uu___287_2655 = env1 in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___287_2655.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___287_2655.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___287_2655.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___287_2655.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___287_2655.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___287_2655.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___287_2655.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___287_2655.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___287_2655.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp = false;
                  FStar_TypeChecker_Env.effects =
                    (uu___287_2655.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___287_2655.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___287_2655.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___287_2655.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___287_2655.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___287_2655.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___287_2655.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___287_2655.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___287_2655.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___287_2655.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___287_2655.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___287_2655.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___287_2655.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___287_2655.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___287_2655.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___287_2655.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___287_2655.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___287_2655.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___287_2655.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___287_2655.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___287_2655.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___287_2655.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___287_2655.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___287_2655.FStar_TypeChecker_Env.dep_graph)
                } in
              let uu____2656 =
                FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
              (match uu____2656 with
               | (ps,w) ->
                   ((let uu____2670 = FStar_ST.op_Bang tacdbg in
                     if uu____2670
                     then
                       let uu____2719 = FStar_Syntax_Print.term_to_string typ in
                       FStar_Util.print1 "Running tactic with goal = %s\n"
                         uu____2719
                     else ());
                    (let uu____2721 = FStar_Tactics_Basic.run tau ps in
                     match uu____2721 with
                     | FStar_Tactics_Result.Success (uu____2730,ps1) ->
                         ((let uu____2733 = FStar_ST.op_Bang tacdbg in
                           if uu____2733
                           then
                             let uu____2782 =
                               FStar_Syntax_Print.term_to_string w in
                             FStar_Util.print1
                               "Tactic generated proofterm %s\n" uu____2782
                           else ());
                          FStar_List.iter
                            (fun g  ->
                               let uu____2789 =
                                 FStar_Tactics_Basic.is_irrelevant g in
                               if uu____2789
                               then
                                 let uu____2790 =
                                   FStar_TypeChecker_Rel.teq_nosmt
                                     g.FStar_Tactics_Types.context
                                     g.FStar_Tactics_Types.witness
                                     FStar_Syntax_Util.exp_unit in
                                 (if uu____2790
                                  then ()
                                  else
                                    (let uu____2792 =
                                       let uu____2793 =
                                         FStar_Syntax_Print.term_to_string
                                           g.FStar_Tactics_Types.witness in
                                       FStar_Util.format1
                                         "Irrelevant tactic witness does not unify with (): %s"
                                         uu____2793 in
                                     failwith uu____2792))
                               else ())
                            (FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals);
                          (let g =
                             let uu___288_2796 =
                               FStar_TypeChecker_Rel.trivial_guard in
                             {
                               FStar_TypeChecker_Env.guard_f =
                                 (uu___288_2796.FStar_TypeChecker_Env.guard_f);
                               FStar_TypeChecker_Env.deferred =
                                 (uu___288_2796.FStar_TypeChecker_Env.deferred);
                               FStar_TypeChecker_Env.univ_ineqs =
                                 (uu___288_2796.FStar_TypeChecker_Env.univ_ineqs);
                               FStar_TypeChecker_Env.implicits =
                                 (ps1.FStar_Tactics_Types.all_implicits)
                             } in
                           let g1 =
                             let uu____2798 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____2798
                               FStar_TypeChecker_Rel.resolve_implicits_tac in
                           report_implicits ps1
                             g1.FStar_TypeChecker_Env.implicits;
                           ((FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals), w)))
                     | FStar_Tactics_Result.Failed (s,ps1) ->
                         ((let uu____2805 =
                             let uu____2806 =
                               FStar_TypeChecker_Normalize.psc_subst
                                 ps1.FStar_Tactics_Types.psc in
                             FStar_Tactics_Types.subst_proof_state uu____2806
                               ps1 in
                           FStar_Tactics_Basic.dump_proofstate uu____2805
                             "at the time of failure");
                          (let uu____2807 =
                             let uu____2808 =
                               let uu____2813 =
                                 FStar_Util.format1 "user tactic failed: %s"
                                   s in
                               (uu____2813, (typ.FStar_Syntax_Syntax.pos)) in
                             FStar_Errors.Error uu____2808 in
                           FStar_Exn.raise uu____2807)))))))
type pol =
  | Pos
  | Neg
  | Both[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____2823 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____2827 -> false
let uu___is_Both: pol -> Prims.bool =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2831 -> false
type 'a tres_m =
  | Unchanged of 'a
  | Simplified of ('a,FStar_Tactics_Types.goal Prims.list)
  FStar_Pervasives_Native.tuple2
  | Dual of ('a,'a,FStar_Tactics_Types.goal Prims.list)
  FStar_Pervasives_Native.tuple3[@@deriving show]
let uu___is_Unchanged: 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2880 -> false
let __proj__Unchanged__item___0: 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0
let uu___is_Simplified: 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2916 -> false
let __proj__Simplified__item___0:
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Types.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0
let uu___is_Dual: 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2966 -> false
let __proj__Dual__item___0:
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Types.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure: 'Auu____3004 . 'Auu____3004 -> 'Auu____3004 tres_m =
  fun x  -> Unchanged x
let flip: pol -> pol =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both
let by_tactic_interp:
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3023 = FStar_Syntax_Util.head_and_args t in
        match uu____3023 with
        | (hd1,args) ->
            let uu____3060 =
              let uu____3073 =
                let uu____3074 = FStar_Syntax_Util.un_uinst hd1 in
                uu____3074.FStar_Syntax_Syntax.n in
              (uu____3073, args) in
            (match uu____3060 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3087))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3150 = run_tactic_on_typ tactic e assertion in
                      (match uu____3150 with
                       | (gs,uu____3158) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3165 = run_tactic_on_typ tactic e assertion in
                      (match uu____3165 with
                       | (gs,uu____3173) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3224 =
                        let uu____3231 =
                          let uu____3234 =
                            let uu____3235 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3235 in
                          [uu____3234] in
                        (FStar_Syntax_Util.t_true, uu____3231) in
                      Simplified uu____3224
                  | Both  ->
                      let uu____3246 =
                        let uu____3259 =
                          let uu____3262 =
                            let uu____3263 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3263 in
                          [uu____3262] in
                        (assertion, FStar_Syntax_Util.t_true, uu____3259) in
                      Dual uu____3246
                  | Neg  -> Simplified (assertion, []))
             | uu____3284 -> Unchanged t)
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
    fun uu___285_3364  ->
      match uu___285_3364 with
      | Unchanged t -> let uu____3370 = f t in Unchanged uu____3370
      | Simplified (t,gs) ->
          let uu____3377 = let uu____3384 = f t in (uu____3384, gs) in
          Simplified uu____3377
      | Dual (tn,tp,gs) ->
          let uu____3394 =
            let uu____3403 = f tn in
            let uu____3404 = f tp in (uu____3403, uu____3404, gs) in
          Dual uu____3394
let comb2: 'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m
  =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3458 = f t1 t2 in Unchanged uu____3458
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3470 = let uu____3477 = f t1 t2 in (uu____3477, gs) in
            Simplified uu____3470
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3491 = let uu____3498 = f t1 t2 in (uu____3498, gs) in
            Simplified uu____3491
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3517 =
              let uu____3524 = f t1 t2 in
              (uu____3524, (FStar_List.append gs1 gs2)) in
            Simplified uu____3517
        | uu____3527 ->
            let uu____3536 = explode x in
            (match uu____3536 with
             | (n1,p1,gs1) ->
                 let uu____3554 = explode y in
                 (match uu____3554 with
                  | (n2,p2,gs2) ->
                      let uu____3572 =
                        let uu____3581 = f n1 n2 in
                        let uu____3582 = f p1 p2 in
                        (uu____3581, uu____3582, (FStar_List.append gs1 gs2)) in
                      Dual uu____3572))
let comb_list: 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3647 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc in
          aux tl1 uu____3647 in
    aux (FStar_List.rev rs) (tpure [])
let emit: 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3690  -> fun x  -> x) (Simplified ((), gs)) m
let rec traverse:
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3724 =
              let uu____3725 = FStar_Syntax_Subst.compress t in
              uu____3725.FStar_Syntax_Syntax.n in
            match uu____3724 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1 in
                let uu____3737 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us)) in
                uu____3737 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1 in
                let uu____3761 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m)) in
                uu____3761 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3779;
                   FStar_Syntax_Syntax.vars = uu____3780;_},(p,uu____3782)::
                 (q,uu____3784)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3824 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3824 in
                let r1 = traverse f (flip pol) e p in
                let r2 =
                  let uu____3827 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f pol uu____3827 q in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3833 = FStar_Syntax_Util.mk_imp l r in
                       uu____3833.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3837;
                   FStar_Syntax_Syntax.vars = uu____3838;_},(p,uu____3840)::
                 (q,uu____3842)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3882 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3882 in
                let xq =
                  let uu____3884 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3884 in
                let r1 =
                  let uu____3886 = FStar_TypeChecker_Env.push_bv e xq in
                  traverse f Both uu____3886 p in
                let r2 =
                  let uu____3888 = FStar_TypeChecker_Env.push_bv e xp in
                  traverse f Both uu____3888 q in
                (match (r1, r2) with
                 | (Unchanged uu____3891,Unchanged uu____3892) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3902 = FStar_Syntax_Util.mk_iff l r in
                            uu____3902.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3905 ->
                     let uu____3910 = explode r1 in
                     (match uu____3910 with
                      | (pn,pp,gs1) ->
                          let uu____3928 = explode r2 in
                          (match uu____3928 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3949 =
                                   FStar_Syntax_Util.mk_imp pn qp in
                                 let uu____3950 =
                                   FStar_Syntax_Util.mk_imp qn pp in
                                 FStar_Syntax_Util.mk_conj uu____3949
                                   uu____3950 in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1 in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4002  ->
                       fun r  ->
                         match uu____4002 with
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
                let uu____4120 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____4120 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let r0 =
                       FStar_List.map
                         (fun uu____4154  ->
                            match uu____4154 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort in
                                let uu____4168 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___289_4192 = bv in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___289_4192.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___289_4192.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq)) in
                                uu____4168 r) bs1 in
                     let rbs = comb_list r0 in
                     let rt = traverse f pol e' topen in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4212 = FStar_Syntax_Util.abs bs2 t2 k in
                            uu____4212.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4258 = traverse f pol e t1 in
                let uu____4263 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef)) in
                uu____4263 uu____4258
            | x -> tpure x in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___290_4301 = t in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___290_4301.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___290_4301.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4308 =
                f pol e
                  (let uu___291_4312 = t in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___291_4312.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___291_4312.FStar_Syntax_Syntax.vars)
                   }) in
              emit gs uu____4308
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___292_4322 = t in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___292_4322.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___292_4322.FStar_Syntax_Syntax.vars)
                   }) in
              let uu____4323 = explode rp in
              (match uu____4323 with
               | (uu____4332,p',gs') ->
                   Dual
                     ((let uu___293_4346 = t in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___293_4346.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___293_4346.FStar_Syntax_Syntax.vars)
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
      (let uu____4381 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____4381);
      (let uu____4431 = FStar_ST.op_Bang tacdbg in
       if uu____4431
       then
         let uu____4480 =
           let uu____4481 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____4481
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____4482 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4480
           uu____4482
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____4511 =
         let uu____4518 = traverse by_tactic_interp Pos env goal in
         match uu____4518 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4536 -> failwith "no" in
       match uu____4511 with
       | (t',gs) ->
           ((let uu____4558 = FStar_ST.op_Bang tacdbg in
             if uu____4558
             then
               let uu____4607 =
                 let uu____4608 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____4608
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____4609 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4607 uu____4609
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4656  ->
                    fun g  ->
                      match uu____4656 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4701 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____4701 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4704 =
                                  let uu____4705 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4705 in
                                failwith uu____4704
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____4708 = FStar_ST.op_Bang tacdbg in
                            if uu____4708
                            then
                              let uu____4757 = FStar_Util.string_of_int n1 in
                              let uu____4758 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4757 uu____4758
                            else ());
                           (let gt' =
                              let uu____4761 =
                                let uu____4762 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____4762 in
                              FStar_TypeChecker_Util.label uu____4761
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____4777 = s1 in
             match uu____4777 with
             | (uu____4798,gs1) ->
                 let uu____4816 =
                   let uu____4823 = FStar_Options.peek () in
                   (env, t', uu____4823) in
                 uu____4816 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____4834 =
        let uu____4835 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____4835 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4834 [FStar_Syntax_Syntax.U_zero] in
    let uu____4836 =
      let uu____4837 =
        let uu____4838 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____4839 =
          let uu____4842 = FStar_Syntax_Syntax.as_arg a in [uu____4842] in
        uu____4838 :: uu____4839 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4837 in
    uu____4836 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4855 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____4855);
        (let uu____4904 =
           let uu____4911 = reify_tactic tau in
           run_tactic_on_typ uu____4911 env typ in
         match uu____4904 with
         | (gs,w) ->
             let uu____4918 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4922 =
                      let uu____4923 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____4923 in
                    Prims.op_Negation uu____4922) gs in
             if uu____4918
             then
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("synthesis left open goals",
                      (typ.FStar_Syntax_Syntax.pos)))
             else w)