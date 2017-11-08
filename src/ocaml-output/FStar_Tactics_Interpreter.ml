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
      let uu___418_1890 = t in
      {
        FStar_Syntax_Syntax.n = (uu___418_1890.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___418_1890.FStar_Syntax_Syntax.vars)
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
              let uu____2294 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2294
            else ());
           (let result =
              let uu____2297 = primitive_steps () in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2297 steps proof_state.FStar_Tactics_Types.main_context
                tm in
            (let uu____2301 = FStar_ST.op_Bang tacdbg in
             if uu____2301
             then
               let uu____2348 = FStar_Syntax_Print.term_to_string result in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2348
             else ());
            (let uu____2350 =
               FStar_Tactics_Embedding.unembed_result result unembed_b in
             match uu____2350 with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2393 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2393
                   (fun uu____2397  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2420 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2420
                   (fun uu____2424  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2437 =
                   let uu____2438 =
                     let uu____2443 =
                       let uu____2444 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____2444 in
                     (uu____2443,
                       ((proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)) in
                   FStar_Errors.Error uu____2438 in
                 FStar_Exn.raise uu____2437)))
and unembed_tactic_0':
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2453 = unembed_tactic_0 unembed_b embedded_tac_b in
      FStar_All.pipe_left (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
        uu____2453
let report_implicits:
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2505  ->
             match uu____2505 with
             | (r,uu____2523,uv,uu____2525,ty,rng) ->
                 let uu____2528 =
                   let uu____2529 = FStar_Syntax_Print.uvar_to_string uv in
                   let uu____2530 = FStar_Syntax_Print.term_to_string ty in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2529 uu____2530 r in
                 (uu____2528, rng)) is in
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
        (let uu____2575 = FStar_ST.op_Bang tacdbg in
         if uu____2575
         then
           let uu____2622 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2622
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         FStar_Errors.stop_if_err ();
         (let tau =
            unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic1 in
          let uu____2629 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____2629 with
          | (env1,uu____2643) ->
              let env2 =
                let uu___419_2649 = env1 in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___419_2649.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___419_2649.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___419_2649.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___419_2649.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___419_2649.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___419_2649.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___419_2649.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___419_2649.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___419_2649.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp = false;
                  FStar_TypeChecker_Env.effects =
                    (uu___419_2649.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___419_2649.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___419_2649.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___419_2649.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___419_2649.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___419_2649.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___419_2649.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___419_2649.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___419_2649.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___419_2649.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___419_2649.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___419_2649.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___419_2649.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___419_2649.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___419_2649.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___419_2649.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___419_2649.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___419_2649.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___419_2649.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___419_2649.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___419_2649.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___419_2649.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___419_2649.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___419_2649.FStar_TypeChecker_Env.dep_graph)
                } in
              let uu____2650 =
                FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
              (match uu____2650 with
               | (ps,w) ->
                   ((let uu____2664 = FStar_ST.op_Bang tacdbg in
                     if uu____2664
                     then
                       let uu____2711 = FStar_Syntax_Print.term_to_string typ in
                       FStar_Util.print1 "Running tactic with goal = %s\n"
                         uu____2711
                     else ());
                    (let uu____2713 = FStar_Tactics_Basic.run tau ps in
                     match uu____2713 with
                     | FStar_Tactics_Result.Success (uu____2722,ps1) ->
                         ((let uu____2725 = FStar_ST.op_Bang tacdbg in
                           if uu____2725
                           then
                             let uu____2772 =
                               FStar_Syntax_Print.term_to_string w in
                             FStar_Util.print1
                               "Tactic generated proofterm %s\n" uu____2772
                           else ());
                          FStar_List.iter
                            (fun g  ->
                               let uu____2779 =
                                 FStar_Tactics_Basic.is_irrelevant g in
                               if uu____2779
                               then
                                 let uu____2780 =
                                   FStar_TypeChecker_Rel.teq_nosmt
                                     g.FStar_Tactics_Types.context
                                     g.FStar_Tactics_Types.witness
                                     FStar_Syntax_Util.exp_unit in
                                 (if uu____2780
                                  then ()
                                  else
                                    (let uu____2782 =
                                       let uu____2783 =
                                         FStar_Syntax_Print.term_to_string
                                           g.FStar_Tactics_Types.witness in
                                       FStar_Util.format1
                                         "Irrelevant tactic witness does not unify with (): %s"
                                         uu____2783 in
                                     failwith uu____2782))
                               else ())
                            (FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals);
                          (let g =
                             let uu___420_2786 =
                               FStar_TypeChecker_Rel.trivial_guard in
                             {
                               FStar_TypeChecker_Env.guard_f =
                                 (uu___420_2786.FStar_TypeChecker_Env.guard_f);
                               FStar_TypeChecker_Env.deferred =
                                 (uu___420_2786.FStar_TypeChecker_Env.deferred);
                               FStar_TypeChecker_Env.univ_ineqs =
                                 (uu___420_2786.FStar_TypeChecker_Env.univ_ineqs);
                               FStar_TypeChecker_Env.implicits =
                                 (ps1.FStar_Tactics_Types.all_implicits)
                             } in
                           let g1 =
                             let uu____2788 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____2788
                               FStar_TypeChecker_Rel.resolve_implicits_tac in
                           report_implicits ps1
                             g1.FStar_TypeChecker_Env.implicits;
                           ((FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals), w)))
                     | FStar_Tactics_Result.Failed (s,ps1) ->
                         ((let uu____2795 =
                             let uu____2796 =
                               FStar_TypeChecker_Normalize.psc_subst
                                 ps1.FStar_Tactics_Types.psc in
                             FStar_Tactics_Types.subst_proof_state uu____2796
                               ps1 in
                           FStar_Tactics_Basic.dump_proofstate uu____2795
                             "at the time of failure");
                          (let uu____2797 =
                             let uu____2798 =
                               let uu____2803 =
                                 FStar_Util.format1 "user tactic failed: %s"
                                   s in
                               (uu____2803, (typ.FStar_Syntax_Syntax.pos)) in
                             FStar_Errors.Error uu____2798 in
                           FStar_Exn.raise uu____2797)))))))
type pol =
  | Pos
  | Neg[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____2813 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____2817 -> false
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
        let uu____2842 = FStar_Syntax_Util.head_and_args t in
        match uu____2842 with
        | (hd1,args) ->
            let uu____2885 =
              let uu____2898 =
                let uu____2899 = FStar_Syntax_Util.un_uinst hd1 in
                uu____2899.FStar_Syntax_Syntax.n in
              (uu____2898, args) in
            (match uu____2885 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2918))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2987 = run_tactic_on_typ tactic e assertion in
                   (match uu____2987 with
                    | (gs,uu____3001) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____3053 =
                     let uu____3056 =
                       let uu____3057 =
                         FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____3057 in
                     [uu____3056] in
                   (FStar_Syntax_Util.t_true, uu____3053)
                 else (assertion, [])
             | uu____3073 -> (t, []))
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
          let uu____3139 =
            let uu____3146 =
              let uu____3147 = FStar_Syntax_Subst.compress t in
              uu____3147.FStar_Syntax_Syntax.n in
            match uu____3146 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____3162 = traverse f pol e t1 in
                (match uu____3162 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____3189 = traverse f pol e t1 in
                (match uu____3189 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3211;
                   FStar_Syntax_Syntax.vars = uu____3212;_},(p,uu____3214)::
                 (q,uu____3216)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3256 = FStar_Syntax_Util.mk_squash p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3256 in
                let uu____3257 = traverse f (flip pol) e p in
                (match uu____3257 with
                 | (p',gs1) ->
                     let uu____3276 =
                       let uu____3283 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____3283 q in
                     (match uu____3276 with
                      | (q',gs2) ->
                          let uu____3296 =
                            let uu____3297 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____3297.FStar_Syntax_Syntax.n in
                          (uu____3296, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____3324 = traverse f pol e hd1 in
                (match uu____3324 with
                 | (hd',gs1) ->
                     let uu____3343 =
                       FStar_List.fold_right
                         (fun uu____3381  ->
                            fun uu____3382  ->
                              match (uu____3381, uu____3382) with
                              | ((a,q),(as',gs)) ->
                                  let uu____3463 = traverse f pol e a in
                                  (match uu____3463 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____3343 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____3567 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____3567 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____3581 =
                       let uu____3596 =
                         FStar_List.map
                           (fun uu____3629  ->
                              match uu____3629 with
                              | (bv,aq) ->
                                  let uu____3646 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____3646 with
                                   | (s',gs) ->
                                       (((let uu___421_3676 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___421_3676.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___421_3676.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____3596 in
                     (match uu____3581 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____3740 = traverse f pol e' topen in
                          (match uu____3740 with
                           | (topen',gs2) ->
                               let uu____3759 =
                                 let uu____3760 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____3760.FStar_Syntax_Syntax.n in
                               (uu____3759, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____3139 with
          | (tn',gs) ->
              let t' =
                let uu___422_3783 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___422_3783.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___422_3783.FStar_Syntax_Syntax.vars)
                } in
              let uu____3784 = f pol e t' in
              (match uu____3784 with
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
      (let uu____3839 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____3839);
      (let uu____3887 = FStar_ST.op_Bang tacdbg in
       if uu____3887
       then
         let uu____3934 =
           let uu____3935 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____3935
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____3936 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3934
           uu____3936
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____3965 = traverse by_tactic_interp Pos env goal in
       match uu____3965 with
       | (t',gs) ->
           ((let uu____3987 = FStar_ST.op_Bang tacdbg in
             if uu____3987
             then
               let uu____4034 =
                 let uu____4035 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____4035
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____4036 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4034 uu____4036
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4083  ->
                    fun g  ->
                      match uu____4083 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4128 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____4128 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4131 =
                                  let uu____4132 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4132 in
                                failwith uu____4131
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____4135 = FStar_ST.op_Bang tacdbg in
                            if uu____4135
                            then
                              let uu____4182 = FStar_Util.string_of_int n1 in
                              let uu____4183 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4182 uu____4183
                            else ());
                           (let gt' =
                              let uu____4186 =
                                let uu____4187 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____4187 in
                              FStar_TypeChecker_Util.label uu____4186
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____4202 = s1 in
             match uu____4202 with
             | (uu____4223,gs1) ->
                 let uu____4241 =
                   let uu____4248 = FStar_Options.peek () in
                   (env, t', uu____4248) in
                 uu____4241 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____4259 =
        let uu____4260 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____4260 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4259 [FStar_Syntax_Syntax.U_zero] in
    let uu____4261 =
      let uu____4262 =
        let uu____4263 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____4264 =
          let uu____4267 = FStar_Syntax_Syntax.as_arg a in [uu____4267] in
        uu____4263 :: uu____4264 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4262 in
    uu____4261 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4280 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____4280);
        (let uu____4327 =
           let uu____4334 = reify_tactic tau in
           run_tactic_on_typ uu____4334 env typ in
         match uu____4327 with
         | (gs,w) ->
             let uu____4341 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4345 =
                      let uu____4346 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____4346 in
                    Prims.op_Negation uu____4345) gs in
             if uu____4341
             then
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("synthesis left open goals",
                      (typ.FStar_Syntax_Syntax.pos)))
             else w)