open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let mk_tactic_interpretation_0 :
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
                    FStar_Tactics_Embedding.unembed_proofstate embedded_state
                     in
                  FStar_Util.bind_opt uu____80
                    (fun ps  ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       FStar_Tactics_Basic.log ps1
                         (fun uu____94  ->
                            let uu____95 = FStar_Ident.string_of_lid nm  in
                            let uu____96 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.print2 "Reached %s, args are: %s\n"
                              uu____95 uu____96);
                       (let res = FStar_Tactics_Basic.run t ps1  in
                        let uu____100 =
                          let uu____101 =
                            FStar_TypeChecker_Normalize.psc_range psc  in
                          let uu____102 =
                            FStar_Tactics_Embedding.embed_result embed_r t_r
                             in
                          uu____102 uu____101 res  in
                        FStar_Pervasives_Native.Some uu____100))
              | uu____116 ->
                  failwith "Unexpected application of tactic primitive"
  
let mk_tactic_interpretation_1 :
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
                | (a,uu____188)::(embedded_state,uu____190)::[] ->
                    let uu____217 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state
                       in
                    FStar_Util.bind_opt uu____217
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____230  ->
                              let uu____231 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____232 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____231 uu____232);
                         (let uu____233 = unembed_a a  in
                          FStar_Util.bind_opt uu____233
                            (fun a1  ->
                               let res =
                                 let uu____245 = t a1  in
                                 FStar_Tactics_Basic.run uu____245 ps1  in
                               let uu____248 =
                                 let uu____249 =
                                   FStar_TypeChecker_Normalize.psc_range psc
                                    in
                                 let uu____250 =
                                   FStar_Tactics_Embedding.embed_result
                                     embed_r t_r
                                    in
                                 uu____250 uu____249 res  in
                               FStar_Pervasives_Native.Some uu____248)))
                | uu____264 ->
                    let uu____265 =
                      let uu____266 = FStar_Ident.string_of_lid nm  in
                      let uu____267 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____266 uu____267
                       in
                    failwith uu____265
  
let mk_tactic_interpretation_1_env :
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
                | (a,uu____344)::(embedded_state,uu____346)::[] ->
                    let uu____373 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state
                       in
                    FStar_Util.bind_opt uu____373
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____386  ->
                              let uu____387 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____388 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____387 uu____388);
                         (let uu____389 = unembed_a a  in
                          FStar_Util.bind_opt uu____389
                            (fun a1  ->
                               let res =
                                 let uu____401 = t psc a1  in
                                 FStar_Tactics_Basic.run uu____401 ps1  in
                               let uu____404 =
                                 let uu____405 =
                                   FStar_TypeChecker_Normalize.psc_range psc
                                    in
                                 let uu____406 =
                                   FStar_Tactics_Embedding.embed_result
                                     embed_r t_r
                                    in
                                 uu____406 uu____405 res  in
                               FStar_Pervasives_Native.Some uu____404)))
                | uu____420 ->
                    let uu____421 =
                      let uu____422 = FStar_Ident.string_of_lid nm  in
                      let uu____423 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____422 uu____423
                       in
                    failwith uu____421
  
let mk_tactic_interpretation_2 :
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
                  | (a,uu____515)::(b,uu____517)::(embedded_state,uu____519)::[]
                      ->
                      let uu____556 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state
                         in
                      FStar_Util.bind_opt uu____556
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____569  ->
                                let uu____570 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____571 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____570
                                  uu____571);
                           (let uu____572 = unembed_a a  in
                            FStar_Util.bind_opt uu____572
                              (fun a1  ->
                                 let uu____580 = unembed_b b  in
                                 FStar_Util.bind_opt uu____580
                                   (fun b1  ->
                                      let res =
                                        let uu____592 = t a1 b1  in
                                        FStar_Tactics_Basic.run uu____592 ps1
                                         in
                                      let uu____595 =
                                        let uu____596 =
                                          FStar_TypeChecker_Normalize.psc_range
                                            psc
                                           in
                                        let uu____597 =
                                          FStar_Tactics_Embedding.embed_result
                                            embed_r t_r
                                           in
                                        uu____597 uu____596 res  in
                                      FStar_Pervasives_Native.Some uu____595))))
                  | uu____611 ->
                      let uu____612 =
                        let uu____613 = FStar_Ident.string_of_lid nm  in
                        let uu____614 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____613 uu____614
                         in
                      failwith uu____612
  
let mk_tactic_interpretation_3 :
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
                    | (a,uu____726)::(b,uu____728)::(c,uu____730)::(embedded_state,uu____732)::[]
                        ->
                        let uu____779 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state
                           in
                        FStar_Util.bind_opt uu____779
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____792  ->
                                  let uu____793 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____794 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state
                                     in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____793
                                    uu____794);
                             (let uu____795 = unembed_a a  in
                              FStar_Util.bind_opt uu____795
                                (fun a1  ->
                                   let uu____803 = unembed_b b  in
                                   FStar_Util.bind_opt uu____803
                                     (fun b1  ->
                                        let uu____811 = unembed_c c  in
                                        FStar_Util.bind_opt uu____811
                                          (fun c1  ->
                                             let res =
                                               let uu____823 = t a1 b1 c1  in
                                               FStar_Tactics_Basic.run
                                                 uu____823 ps1
                                                in
                                             let uu____826 =
                                               let uu____827 =
                                                 FStar_TypeChecker_Normalize.psc_range
                                                   psc
                                                  in
                                               let uu____828 =
                                                 FStar_Tactics_Embedding.embed_result
                                                   embed_r t_r
                                                  in
                                               uu____828 uu____827 res  in
                                             FStar_Pervasives_Native.Some
                                               uu____826)))))
                    | uu____842 ->
                        let uu____843 =
                          let uu____844 = FStar_Ident.string_of_lid nm  in
                          let uu____845 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____844 uu____845
                           in
                        failwith uu____843
  
let mk_tactic_interpretation_5 :
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
                        | (a,uu____997)::(b,uu____999)::(c,uu____1001)::
                            (d,uu____1003)::(e,uu____1005)::(embedded_state,uu____1007)::[]
                            ->
                            let uu____1074 =
                              FStar_Tactics_Embedding.unembed_proofstate
                                embedded_state
                               in
                            FStar_Util.bind_opt uu____1074
                              (fun ps  ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1087  ->
                                      let uu____1088 =
                                        FStar_Ident.string_of_lid nm  in
                                      let uu____1089 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state
                                         in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1088 uu____1089);
                                 (let uu____1090 = unembed_a a  in
                                  FStar_Util.bind_opt uu____1090
                                    (fun a1  ->
                                       let uu____1098 = unembed_b b  in
                                       FStar_Util.bind_opt uu____1098
                                         (fun b1  ->
                                            let uu____1106 = unembed_c c  in
                                            FStar_Util.bind_opt uu____1106
                                              (fun c1  ->
                                                 let uu____1114 = unembed_d d
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____1114
                                                   (fun d1  ->
                                                      let uu____1122 =
                                                        unembed_e e  in
                                                      FStar_Util.bind_opt
                                                        uu____1122
                                                        (fun e1  ->
                                                           let res =
                                                             let uu____1134 =
                                                               t a1 b1 c1 d1
                                                                 e1
                                                                in
                                                             FStar_Tactics_Basic.run
                                                               uu____1134 ps1
                                                              in
                                                           let uu____1137 =
                                                             let uu____1138 =
                                                               FStar_TypeChecker_Normalize.psc_range
                                                                 psc
                                                                in
                                                             let uu____1139 =
                                                               FStar_Tactics_Embedding.embed_result
                                                                 embed_r t_r
                                                                in
                                                             uu____1139
                                                               uu____1138 res
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1137)))))))
                        | uu____1153 ->
                            let uu____1154 =
                              let uu____1155 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____1156 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1155 uu____1156
                               in
                            failwith uu____1154
  
let mk_total_interpretation_1 :
  'a 'r .
    ('a -> 'r) ->
      'a FStar_Syntax_Embeddings.unembedder ->
        'r FStar_Syntax_Embeddings.embedder ->
          FStar_Syntax_Syntax.typ ->
            FStar_Ident.lid ->
              FStar_TypeChecker_Normalize.psc ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun f  ->
    fun unembed_a  ->
      fun embed_r  ->
        fun t_r  ->
          fun nm  ->
            fun psc  ->
              fun args  ->
                mk_tactic_interpretation_1
                  (fun x  ->
                     let uu____1226 = f x  in
                     FStar_Tactics_Basic.ret uu____1226) unembed_a embed_r
                  t_r nm psc args
  
let mk_total_interpretation_2 :
  'a 'b 'r .
    ('a -> 'b -> 'r) ->
      'a FStar_Syntax_Embeddings.unembedder ->
        'b FStar_Syntax_Embeddings.unembedder ->
          'r FStar_Syntax_Embeddings.embedder ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_TypeChecker_Normalize.psc ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun f  ->
    fun unembed_a  ->
      fun unembed_b  ->
        fun embed_r  ->
          fun t_r  ->
            fun nm  ->
              fun psc  ->
                fun args  ->
                  mk_tactic_interpretation_2
                    (fun x  ->
                       fun y  ->
                         let uu____1326 = f x y  in
                         FStar_Tactics_Basic.ret uu____1326) unembed_a
                    unembed_b embed_r t_r nm psc args
  
let (step_from_native_step :
  FStar_Tactics_Native.native_primitive_step ->
    FStar_TypeChecker_Normalize.primitive_step)
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
  
let rec (primitive_steps :
  Prims.unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  fun uu____1390  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm]
         in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation =
          (fun psc  -> fun args  -> interpretation nm1 psc args)
      }  in
    let native_tactics = FStar_Tactics_Native.list_all ()  in
    let native_tactics_steps =
      FStar_List.map step_from_native_step native_tactics  in
    let mktac0 r name f e_r tr =
      mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 f e_r tr)
       in
    let mktac1 a r name f u_a e_r tr =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 f u_a e_r tr)
       in
    let mktac2 a b r name f u_a u_b e_r tr =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 f u_a u_b e_r tr)
       in
    let mktac3 a b c r name f u_a u_b u_c e_r tr =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 f u_a u_b u_c e_r tr)
       in
    let mktac5 a b c d e r name f u_a u_b u_c u_d u_e e_r tr =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 f u_a u_b u_c u_d u_e e_r tr)
       in
    let mktot1 a r name f u_a e_r tr =
      mk1 name (Prims.parse_int "2") (mk_total_interpretation_1 f u_a e_r tr)
       in
    let mktot2 a b r name f u_a u_b e_r tr =
      mk1 name (Prims.parse_int "3")
        (mk_total_interpretation_2 f u_a u_b e_r tr)
       in
    let decr_depth_interp psc args =
      match args with
      | (ps,uu____2011)::[] ->
          let uu____2028 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2028
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2036 =
                 let uu____2037 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2038 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____2037
                   uu____2038
                  in
               FStar_Pervasives_Native.Some uu____2036)
      | uu____2039 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____2043 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2043;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____2056)::[] ->
          let uu____2073 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2073
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____2081 =
                 let uu____2082 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____2083 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____2082
                   uu____2083
                  in
               FStar_Pervasives_Native.Some uu____2081)
      | uu____2084 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____2088 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____2088;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____2105)::[] ->
          let uu____2122 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2122
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____2135 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____2152)::(r,uu____2154)::[] ->
          let uu____2181 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____2181
            (fun ps1  ->
               let uu____2187 = FStar_Syntax_Embeddings.unembed_range r  in
               FStar_Util.bind_opt uu____2187
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____2195 =
                      let uu____2196 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Tactics_Embedding.embed_proofstate uu____2196 ps'
                       in
                    FStar_Pervasives_Native.Some uu____2195))
      | uu____2197 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let set_proofstate_range_step =
      let nm =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation =
          set_proofstate_range_interp
      }  in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint"  in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      }  in
    let put1 rng t =
      let uu___58_2211 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___58_2211.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___58_2211.FStar_Syntax_Syntax.vars)
      }  in
    let get1 t = FStar_Pervasives_Native.Some t  in
    let uu____2218 =
      let uu____2221 =
        mktac2 () () () "__fail"
          (fun a415  ->
             fun a416  ->
               (Obj.magic (fun uu____2223  -> FStar_Tactics_Basic.fail)) a415
                 a416) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit
         in
      let uu____2224 =
        let uu____2227 =
          mktac0 () "__trivial" (Obj.magic FStar_Tactics_Basic.trivial)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit
           in
        let uu____2228 =
          let uu____2231 =
            let uu____2232 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit
               in
            mktac2 () () () "__trytac"
              (fun a417  ->
                 fun a418  ->
                   (Obj.magic (fun uu____2238  -> FStar_Tactics_Basic.trytac))
                     a417 a418) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____2232)
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2245 =
            let uu____2248 =
              mktac0 () "__intro" (Obj.magic FStar_Tactics_Basic.intro)
                (Obj.magic FStar_Reflection_Embeddings.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder
               in
            let uu____2249 =
              let uu____2252 =
                let uu____2253 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                let uu____2260 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                mktac0 () "__intro_rec"
                  (Obj.magic FStar_Tactics_Basic.intro_rec)
                  (Obj.magic uu____2253) uu____2260
                 in
              let uu____2267 =
                let uu____2270 =
                  let uu____2271 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step
                     in
                  mktac1 () () "__norm"
                    (fun a419  -> (Obj.magic FStar_Tactics_Basic.norm) a419)
                    (Obj.magic uu____2271)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit
                   in
                let uu____2280 =
                  let uu____2283 =
                    let uu____2284 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step
                       in
                    mktac3 () () () () "__norm_term_env"
                      (fun a420  ->
                         fun a421  ->
                           fun a422  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a420 a421 a422)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_env)
                      (Obj.magic uu____2284)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_term)
                      (Obj.magic FStar_Reflection_Embeddings.embed_term)
                      FStar_Syntax_Syntax.t_term
                     in
                  let uu____2293 =
                    let uu____2296 =
                      let uu____2297 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step
                         in
                      mktac2 () () () "__norm_binder_type"
                        (fun a423  ->
                           fun a424  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a423 a424) (Obj.magic uu____2297)
                        (Obj.magic FStar_Reflection_Embeddings.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2306 =
                      let uu____2309 =
                        mktac2 () () () "__rename_to"
                          (fun a425  ->
                             fun a426  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a425
                                 a426)
                          (Obj.magic
                             FStar_Reflection_Embeddings.unembed_binder)
                          (Obj.magic FStar_Syntax_Embeddings.unembed_string)
                          (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                          FStar_Syntax_Syntax.t_unit
                         in
                      let uu____2310 =
                        let uu____2313 =
                          mktac1 () () "__binder_retype"
                            (fun a427  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a427)
                            (Obj.magic
                               FStar_Reflection_Embeddings.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit
                           in
                        let uu____2314 =
                          let uu____2317 =
                            mktac0 () "__revert"
                              (Obj.magic FStar_Tactics_Basic.revert)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit
                             in
                          let uu____2318 =
                            let uu____2321 =
                              mktac0 () "__clear_top"
                                (Obj.magic FStar_Tactics_Basic.clear_top)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit
                               in
                            let uu____2322 =
                              let uu____2325 =
                                mktac1 () () "__clear"
                                  (fun a428  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a428)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.unembed_binder)
                                  (Obj.magic
                                     FStar_Syntax_Embeddings.embed_unit)
                                  FStar_Syntax_Syntax.t_unit
                                 in
                              let uu____2326 =
                                let uu____2329 =
                                  mktac1 () () "__rewrite"
                                    (fun a429  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a429)
                                    (Obj.magic
                                       FStar_Reflection_Embeddings.unembed_binder)
                                    (Obj.magic
                                       FStar_Syntax_Embeddings.embed_unit)
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                let uu____2330 =
                                  let uu____2333 =
                                    mktac0 () "__smt"
                                      (Obj.magic FStar_Tactics_Basic.smt)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit
                                     in
                                  let uu____2334 =
                                    let uu____2337 =
                                      mktac0 () "__refine_intro"
                                        (Obj.magic
                                           FStar_Tactics_Basic.refine_intro)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit
                                       in
                                    let uu____2338 =
                                      let uu____2341 =
                                        mktac3 () () () () "__t_exact"
                                          (fun a430  ->
                                             fun a431  ->
                                               fun a432  ->
                                                 (Obj.magic
                                                    FStar_Tactics_Basic.t_exact)
                                                   a430 a431 a432)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Reflection_Embeddings.unembed_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.embed_unit)
                                          FStar_Syntax_Syntax.t_unit
                                         in
                                      let uu____2342 =
                                        let uu____2345 =
                                          mktac1 () () "__apply"
                                            (fun a433  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a433)
                                            (Obj.magic
                                               FStar_Reflection_Embeddings.unembed_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_unit)
                                            FStar_Syntax_Syntax.t_unit
                                           in
                                        let uu____2346 =
                                          let uu____2349 =
                                            mktac1 () () "__apply_raw"
                                              (fun a434  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a434)
                                              (Obj.magic
                                                 FStar_Reflection_Embeddings.unembed_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.embed_unit)
                                              FStar_Syntax_Syntax.t_unit
                                             in
                                          let uu____2350 =
                                            let uu____2353 =
                                              mktac1 () () "__apply_lemma"
                                                (fun a435  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a435)
                                                (Obj.magic
                                                   FStar_Reflection_Embeddings.unembed_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.embed_unit)
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            let uu____2354 =
                                              let uu____2357 =
                                                let uu____2358 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a436  ->
                                                     fun a437  ->
                                                       fun a438  ->
                                                         fun a439  ->
                                                           fun a440  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2367
                                                                    ->
                                                                   fun
                                                                    uu____2368
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a436 a437 a438
                                                               a439 a440)
                                                  (Obj.magic get1)
                                                  (Obj.magic get1)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.unembed_int)
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic uu____2358)
                                                  FStar_Syntax_Syntax.t_unit
                                                 in
                                              let uu____2375 =
                                                let uu____2378 =
                                                  mktac1 () ()
                                                    "__set_options"
                                                    (fun a441  ->
                                                       (Obj.magic
                                                          FStar_Tactics_Basic.set_options)
                                                         a441)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.unembed_string)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.embed_unit)
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                let uu____2379 =
                                                  let uu____2382 =
                                                    mktac2 () () () "__seq"
                                                      (fun a442  ->
                                                         fun a443  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.seq)
                                                             a442 a443)
                                                      (Obj.magic
                                                         (unembed_tactic_0'
                                                            FStar_Syntax_Embeddings.unembed_unit))
                                                      (Obj.magic
                                                         (unembed_tactic_0'
                                                            FStar_Syntax_Embeddings.unembed_unit))
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.embed_unit)
                                                      FStar_Syntax_Syntax.t_unit
                                                     in
                                                  let uu____2383 =
                                                    let uu____2386 =
                                                      mktac1 () () "__tc"
                                                        (fun a444  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a444)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.unembed_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.embed_term)
                                                        FStar_Syntax_Syntax.t_term
                                                       in
                                                    let uu____2387 =
                                                      let uu____2390 =
                                                        mktac1 () ()
                                                          "__unshelve"
                                                          (fun a445  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a445)
                                                          (Obj.magic
                                                             FStar_Reflection_Embeddings.unembed_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.embed_unit)
                                                          FStar_Syntax_Syntax.t_unit
                                                         in
                                                      let uu____2391 =
                                                        let uu____2394 =
                                                          mktac2 () () ()
                                                            "__unquote"
                                                            (fun a446  ->
                                                               fun a447  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a446 a447)
                                                            (Obj.magic get1)
                                                            (Obj.magic
                                                               FStar_Reflection_Embeddings.unembed_term)
                                                            (Obj.magic put1)
                                                            FStar_Syntax_Syntax.t_unit
                                                           in
                                                        let uu____2395 =
                                                          let uu____2398 =
                                                            mktac1 () ()
                                                              "__prune"
                                                              (fun a448  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a448)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.unembed_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.embed_unit)
                                                              FStar_Syntax_Syntax.t_unit
                                                             in
                                                          let uu____2399 =
                                                            let uu____2402 =
                                                              mktac1 () ()
                                                                "__addns"
                                                                (fun a449  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a449)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.embed_unit)
                                                                FStar_Syntax_Syntax.t_unit
                                                               in
                                                            let uu____2403 =
                                                              let uu____2406
                                                                =
                                                                mktac1 () ()
                                                                  "__print"
                                                                  (fun a450 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun x 
                                                                    ->
                                                                    FStar_Tactics_Basic.tacprint
                                                                    x;
                                                                    FStar_Tactics_Basic.ret
                                                                    ())) a450)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                  FStar_Syntax_Syntax.t_unit
                                                                 in
                                                              let uu____2411
                                                                =
                                                                let uu____2414
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "__dump"
                                                                    (
                                                                    fun a451 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a451)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                   in
                                                                let uu____2415
                                                                  =
                                                                  let uu____2418
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__dump1"
                                                                    (fun a452
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a452)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                  let uu____2419
                                                                    =
                                                                    let uu____2422
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a453
                                                                     ->
                                                                    fun a454 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a453 a454)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_direction)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2423
                                                                    =
                                                                    let uu____2426
                                                                    =
                                                                    mktac0 ()
                                                                    "__trefl"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2427
                                                                    =
                                                                    let uu____2430
                                                                    =
                                                                    mktac0 ()
                                                                    "__later"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2431
                                                                    =
                                                                    let uu____2434
                                                                    =
                                                                    mktac0 ()
                                                                    "__dup"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2435
                                                                    =
                                                                    let uu____2438
                                                                    =
                                                                    mktac0 ()
                                                                    "__flip"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2439
                                                                    =
                                                                    let uu____2442
                                                                    =
                                                                    mktac0 ()
                                                                    "__qed"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2443
                                                                    =
                                                                    let uu____2446
                                                                    =
                                                                    let uu____2447
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2454
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "__cases"
                                                                    (fun a455
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a455)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    uu____2447)
                                                                    uu____2454
                                                                     in
                                                                    let uu____2461
                                                                    =
                                                                    let uu____2464
                                                                    =
                                                                    mktac0 ()
                                                                    "__top_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2465
                                                                    =
                                                                    let uu____2468
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2469
                                                                    =
                                                                    let uu____2472
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_goal"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2473
                                                                    =
                                                                    let uu____2476
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_witness"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2477
                                                                    =
                                                                    let uu____2480
                                                                    =
                                                                    mktac0 ()
                                                                    "__is_guard"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2481
                                                                    =
                                                                    let uu____2484
                                                                    =
                                                                    let uu____2485
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Embeddings.unembed_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__uvar_env"
                                                                    (fun a456
                                                                     ->
                                                                    fun a457 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a456 a457)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_env)
                                                                    (Obj.magic
                                                                    uu____2485)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2494
                                                                    =
                                                                    let uu____2497
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__unify"
                                                                    (fun a458
                                                                     ->
                                                                    fun a459 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a458 a459)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2498
                                                                    =
                                                                    let uu____2501
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "__launch_process"
                                                                    (fun a460
                                                                     ->
                                                                    fun a461 
                                                                    ->
                                                                    fun a462 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a460 a461
                                                                    a462)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_string)
                                                                    FStar_Syntax_Syntax.t_string
                                                                     in
                                                                    let uu____2502
                                                                    =
                                                                    let uu____2505
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__fresh_binder_named"
                                                                    (fun a463
                                                                     ->
                                                                    fun a464 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh_binder_named)
                                                                    a463 a464)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_binder)
                                                                    FStar_Syntax_Syntax.t_binder
                                                                     in
                                                                    let uu____2506
                                                                    =
                                                                    let uu____2509
                                                                    =
                                                                    mktot1 ()
                                                                    ()
                                                                    "__inspect"
                                                                    (fun a465
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.inspect)
                                                                    a465)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term_view)
                                                                    FStar_Reflection_Data.fstar_refl_term_view
                                                                     in
                                                                    let uu____2510
                                                                    =
                                                                    let uu____2513
                                                                    =
                                                                    mktot1 ()
                                                                    ()
                                                                    "__pack"
                                                                    (fun a466
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.pack)
                                                                    a466)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term_view)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2514
                                                                    =
                                                                    let uu____2517
                                                                    =
                                                                    let uu____2518
                                                                    =
                                                                    FStar_Syntax_Syntax.t_list_of
                                                                    FStar_Syntax_Syntax.t_string
                                                                     in
                                                                    mktot1 ()
                                                                    ()
                                                                    "__inspect_fv"
                                                                    (fun a467
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.inspect_fv)
                                                                    a467)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_fvar)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_string_list)
                                                                    uu____2518
                                                                     in
                                                                    let uu____2519
                                                                    =
                                                                    let uu____2522
                                                                    =
                                                                    let uu____2523
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_list
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                     in
                                                                    mktot1 ()
                                                                    ()
                                                                    "__pack_fv"
                                                                    (fun a468
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.pack_fv)
                                                                    a468)
                                                                    (Obj.magic
                                                                    uu____2523)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_fvar)
                                                                    FStar_Reflection_Data.fstar_refl_fv
                                                                     in
                                                                    let uu____2532
                                                                    =
                                                                    let uu____2535
                                                                    =
                                                                    mktot1 ()
                                                                    ()
                                                                    "__inspect_comp"
                                                                    (fun a469
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.inspect_comp)
                                                                    a469)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_comp)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_comp_view)
                                                                    FStar_Reflection_Data.fstar_refl_comp_view
                                                                     in
                                                                    let uu____2536
                                                                    =
                                                                    let uu____2539
                                                                    =
                                                                    mktot1 ()
                                                                    ()
                                                                    "__pack_comp"
                                                                    (fun a470
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.pack_comp)
                                                                    a470)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_comp_view)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_comp)
                                                                    FStar_Reflection_Data.fstar_refl_comp
                                                                     in
                                                                    let uu____2540
                                                                    =
                                                                    let uu____2543
                                                                    =
                                                                    mktot1 ()
                                                                    ()
                                                                    "__inspect_sigelt"
                                                                    (fun a471
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.inspect_sigelt)
                                                                    a471)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_sigelt)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_sigelt_view)
                                                                    FStar_Reflection_Data.fstar_refl_sigelt_view
                                                                     in
                                                                    let uu____2544
                                                                    =
                                                                    let uu____2547
                                                                    =
                                                                    mktot1 ()
                                                                    ()
                                                                    "__pack_sigelt"
                                                                    (fun a472
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.pack_sigelt)
                                                                    a472)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_sigelt_view)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_sigelt)
                                                                    FStar_Reflection_Data.fstar_refl_sigelt
                                                                     in
                                                                    let uu____2548
                                                                    =
                                                                    let uu____2551
                                                                    =
                                                                    mktot1 ()
                                                                    ()
                                                                    "__inspect_bv"
                                                                    (fun a473
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.inspect_bv)
                                                                    a473)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_binder)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_string)
                                                                    FStar_Syntax_Syntax.t_string
                                                                     in
                                                                    let uu____2552
                                                                    =
                                                                    let uu____2555
                                                                    =
                                                                    mktot2 ()
                                                                    () ()
                                                                    "__compare_binder"
                                                                    (fun a474
                                                                     ->
                                                                    fun a475 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.compare_binder)
                                                                    a474 a475)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_binder)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_binder)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_order)
                                                                    FStar_Syntax_Syntax.t_order
                                                                     in
                                                                    let uu____2556
                                                                    =
                                                                    let uu____2559
                                                                    =
                                                                    mktot1 ()
                                                                    ()
                                                                    "__type_of_binder"
                                                                    (fun a476
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.type_of_binder)
                                                                    a476)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_binder)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2560
                                                                    =
                                                                    let uu____2563
                                                                    =
                                                                    mktot2 ()
                                                                    () ()
                                                                    "__is_free"
                                                                    (fun a477
                                                                     ->
                                                                    fun a478 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.is_free)
                                                                    a477 a478)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_binder)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2564
                                                                    =
                                                                    let uu____2567
                                                                    =
                                                                    mktot2 ()
                                                                    () ()
                                                                    "__term_eq"
                                                                    (fun a479
                                                                     ->
                                                                    fun a480 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.term_eq)
                                                                    a479 a480)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2568
                                                                    =
                                                                    let uu____2571
                                                                    =
                                                                    mktot1 ()
                                                                    ()
                                                                    "__term_to_string"
                                                                    (fun a481
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.term_to_string)
                                                                    a481)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_string)
                                                                    FStar_Syntax_Syntax.t_string
                                                                     in
                                                                    let uu____2572
                                                                    =
                                                                    let uu____2575
                                                                    =
                                                                    let uu____2576
                                                                    =
                                                                    FStar_Syntax_Syntax.t_list_of
                                                                    FStar_Reflection_Data.fstar_refl_binder
                                                                     in
                                                                    mktot1 ()
                                                                    ()
                                                                    "__binders_of_env"
                                                                    (fun a482
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.binders_of_env)
                                                                    a482)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_binders)
                                                                    uu____2576
                                                                     in
                                                                    let uu____2577
                                                                    =
                                                                    let uu____2580
                                                                    =
                                                                    let uu____2581
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_option
                                                                    FStar_Reflection_Embeddings.embed_sigelt
                                                                    FStar_Reflection_Data.fstar_refl_sigelt
                                                                     in
                                                                    let uu____2586
                                                                    =
                                                                    FStar_Syntax_Syntax.t_list_of
                                                                    FStar_Syntax_Syntax.t_string
                                                                     in
                                                                    mktot2 ()
                                                                    () ()
                                                                    "__lookup_typ"
                                                                    (fun a483
                                                                     ->
                                                                    fun a484 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.lookup_typ)
                                                                    a483 a484)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_env)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string_list)
                                                                    (Obj.magic
                                                                    uu____2581)
                                                                    uu____2586
                                                                     in
                                                                    [uu____2580;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step]
                                                                     in
                                                                    uu____2575
                                                                    ::
                                                                    uu____2577
                                                                     in
                                                                    uu____2571
                                                                    ::
                                                                    uu____2572
                                                                     in
                                                                    uu____2567
                                                                    ::
                                                                    uu____2568
                                                                     in
                                                                    uu____2563
                                                                    ::
                                                                    uu____2564
                                                                     in
                                                                    uu____2559
                                                                    ::
                                                                    uu____2560
                                                                     in
                                                                    uu____2555
                                                                    ::
                                                                    uu____2556
                                                                     in
                                                                    uu____2551
                                                                    ::
                                                                    uu____2552
                                                                     in
                                                                    uu____2547
                                                                    ::
                                                                    uu____2548
                                                                     in
                                                                    uu____2543
                                                                    ::
                                                                    uu____2544
                                                                     in
                                                                    uu____2539
                                                                    ::
                                                                    uu____2540
                                                                     in
                                                                    uu____2535
                                                                    ::
                                                                    uu____2536
                                                                     in
                                                                    uu____2522
                                                                    ::
                                                                    uu____2532
                                                                     in
                                                                    uu____2517
                                                                    ::
                                                                    uu____2519
                                                                     in
                                                                    uu____2513
                                                                    ::
                                                                    uu____2514
                                                                     in
                                                                    uu____2509
                                                                    ::
                                                                    uu____2510
                                                                     in
                                                                    uu____2505
                                                                    ::
                                                                    uu____2506
                                                                     in
                                                                    uu____2501
                                                                    ::
                                                                    uu____2502
                                                                     in
                                                                    uu____2497
                                                                    ::
                                                                    uu____2498
                                                                     in
                                                                    uu____2484
                                                                    ::
                                                                    uu____2494
                                                                     in
                                                                    uu____2480
                                                                    ::
                                                                    uu____2481
                                                                     in
                                                                    uu____2476
                                                                    ::
                                                                    uu____2477
                                                                     in
                                                                    uu____2472
                                                                    ::
                                                                    uu____2473
                                                                     in
                                                                    uu____2468
                                                                    ::
                                                                    uu____2469
                                                                     in
                                                                    uu____2464
                                                                    ::
                                                                    uu____2465
                                                                     in
                                                                    uu____2446
                                                                    ::
                                                                    uu____2461
                                                                     in
                                                                    uu____2442
                                                                    ::
                                                                    uu____2443
                                                                     in
                                                                    uu____2438
                                                                    ::
                                                                    uu____2439
                                                                     in
                                                                    uu____2434
                                                                    ::
                                                                    uu____2435
                                                                     in
                                                                    uu____2430
                                                                    ::
                                                                    uu____2431
                                                                     in
                                                                    uu____2426
                                                                    ::
                                                                    uu____2427
                                                                     in
                                                                    uu____2422
                                                                    ::
                                                                    uu____2423
                                                                     in
                                                                  uu____2418
                                                                    ::
                                                                    uu____2419
                                                                   in
                                                                uu____2414 ::
                                                                  uu____2415
                                                                 in
                                                              uu____2406 ::
                                                                uu____2411
                                                               in
                                                            uu____2402 ::
                                                              uu____2403
                                                             in
                                                          uu____2398 ::
                                                            uu____2399
                                                           in
                                                        uu____2394 ::
                                                          uu____2395
                                                         in
                                                      uu____2390 ::
                                                        uu____2391
                                                       in
                                                    uu____2386 :: uu____2387
                                                     in
                                                  uu____2382 :: uu____2383
                                                   in
                                                uu____2378 :: uu____2379  in
                                              uu____2357 :: uu____2375  in
                                            uu____2353 :: uu____2354  in
                                          uu____2349 :: uu____2350  in
                                        uu____2345 :: uu____2346  in
                                      uu____2341 :: uu____2342  in
                                    uu____2337 :: uu____2338  in
                                  uu____2333 :: uu____2334  in
                                uu____2329 :: uu____2330  in
                              uu____2325 :: uu____2326  in
                            uu____2321 :: uu____2322  in
                          uu____2317 :: uu____2318  in
                        uu____2313 :: uu____2314  in
                      uu____2309 :: uu____2310  in
                    uu____2296 :: uu____2306  in
                  uu____2283 :: uu____2293  in
                uu____2270 :: uu____2280  in
              uu____2252 :: uu____2267  in
            uu____2248 :: uu____2249  in
          uu____2231 :: uu____2245  in
        uu____2227 :: uu____2228  in
      uu____2221 :: uu____2224  in
    FStar_List.append uu____2218 native_tactics_steps

and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term -> 'Ab FStar_Tactics_Basic.tac
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
        (fun proof_state  ->
           let rng = embedded_tac_b.FStar_Syntax_Syntax.pos  in
           let tm =
             let uu____2615 =
               let uu____2616 =
                 let uu____2617 =
                   let uu____2618 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____2618  in
                 [uu____2617]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2616  in
             uu____2615 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____2625 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____2625
            then
              let uu____2626 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2626
            else ());
           (let result =
              let uu____2629 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2629 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____2633 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____2633
             then
               let uu____2634 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2634
             else ());
            (let res =
               FStar_Tactics_Embedding.unembed_result result unembed_b  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2679 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2679
                   (fun uu____2683  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2706 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2706
                   (fun uu____2710  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2723 =
                   let uu____2728 =
                     let uu____2729 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2729
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2728)  in
                 FStar_Errors.raise_error uu____2723
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2738 = unembed_tactic_0 unembed_b embedded_tac_b  in
      FStar_All.pipe_left (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
        uu____2738

let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2794  ->
             match uu____2794 with
             | (r,uu____2814,uv,uu____2816,ty,rng) ->
                 let uu____2819 =
                   let uu____2820 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____2821 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2820 uu____2821 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____2819, rng)) is
         in
      match errs with
      | [] -> ()
      | (e,msg,r)::tl1 ->
          (FStar_Tactics_Basic.dump_proofstate ps
             "failing due to uninstantiated implicits";
           FStar_Errors.add_errors tl1;
           FStar_Errors.raise_error (e, msg) r)
  
let (run_tactic_on_typ :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Tactics_Basic.goal Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun tactic  ->
    fun env  ->
      fun typ  ->
        (let uu____2870 = FStar_ST.op_Bang tacdbg  in
         if uu____2870
         then
           let uu____2890 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2890
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         (let uu____2894 = FStar_ST.op_Bang tacdbg  in
          if uu____2894
          then
            let uu____2914 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____2914
          else ());
         (let uu____2916 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
          match uu____2916 with
          | (uu____2929,uu____2930,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic1
                   in
                let uu____2937 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                match uu____2937 with
                | (env1,uu____2951) ->
                    let env2 =
                      let uu___59_2957 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___59_2957.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___59_2957.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___59_2957.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___59_2957.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___59_2957.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___59_2957.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___59_2957.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___59_2957.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___59_2957.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___59_2957.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___59_2957.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___59_2957.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___59_2957.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___59_2957.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___59_2957.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___59_2957.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___59_2957.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___59_2957.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___59_2957.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___59_2957.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___59_2957.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___59_2957.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___59_2957.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___59_2957.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___59_2957.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___59_2957.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___59_2957.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___59_2957.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth =
                          (uu___59_2957.FStar_TypeChecker_Env.synth);
                        FStar_TypeChecker_Env.splice =
                          (uu___59_2957.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___59_2957.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___59_2957.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___59_2957.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___59_2957.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___59_2957.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let uu____2958 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ  in
                    (match uu____2958 with
                     | (ps,w) ->
                         ((let uu____2972 = FStar_ST.op_Bang tacdbg  in
                           if uu____2972
                           then
                             let uu____2992 =
                               FStar_Syntax_Print.term_to_string typ  in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____2992
                           else ());
                          (let uu____2994 =
                             FStar_Util.record_time
                               (fun uu____3004  ->
                                  FStar_Tactics_Basic.run tau ps)
                              in
                           match uu____2994 with
                           | (res,ms) ->
                               ((let uu____3018 = FStar_ST.op_Bang tacdbg  in
                                 if uu____3018
                                 then
                                   let uu____3038 =
                                     FStar_Util.string_of_int ms  in
                                   FStar_Util.print1
                                     "Tactic ran in %s milliseconds\n"
                                     uu____3038
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____3046,ps1) ->
                                     ((let uu____3049 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____3049
                                       then
                                         let uu____3069 =
                                           FStar_Syntax_Print.term_to_string
                                             w
                                            in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____3069
                                       else ());
                                      FStar_List.iter
                                        (fun g1  ->
                                           let uu____3076 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____3076
                                           then
                                             let uu____3077 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____3077
                                              then ()
                                              else
                                                (let uu____3079 =
                                                   let uu____3080 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____3080
                                                    in
                                                 failwith uu____3079))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___60_3083 =
                                           FStar_TypeChecker_Rel.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___60_3083.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___60_3083.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___60_3083.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         let uu____3085 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env2 g1
                                            in
                                         FStar_All.pipe_right uu____3085
                                           FStar_TypeChecker_Rel.resolve_implicits_tac
                                          in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s,ps1) ->
                                     ((let uu____3092 =
                                         let uu____3093 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____3093 ps1
                                          in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____3092 "at the time of failure");
                                      (let uu____3094 =
                                         let uu____3099 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s
                                            in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____3099)
                                          in
                                       FStar_Errors.raise_error uu____3094
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____3109 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____3113 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____3117 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____3166 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3202 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3252 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3290 . 'Auu____3290 -> 'Auu____3290 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3309 = FStar_Syntax_Util.head_and_args t  in
        match uu____3309 with
        | (hd1,args) ->
            let uu____3346 =
              let uu____3359 =
                let uu____3360 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3360.FStar_Syntax_Syntax.n  in
              (uu____3359, args)  in
            (match uu____3346 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3373))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3436 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3436 with
                       | (gs,uu____3444) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3451 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3451 with
                       | (gs,uu____3459) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3510 =
                        let uu____3517 =
                          let uu____3520 =
                            let uu____3521 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3521
                             in
                          [uu____3520]  in
                        (FStar_Syntax_Util.t_true, uu____3517)  in
                      Simplified uu____3510
                  | Both  ->
                      let uu____3532 =
                        let uu____3545 =
                          let uu____3548 =
                            let uu____3549 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3549
                             in
                          [uu____3548]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3545)  in
                      Dual uu____3532
                  | Neg  -> Simplified (assertion, []))
             | uu____3570 -> Unchanged t)
  
let explode :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___57_3650  ->
      match uu___57_3650 with
      | Unchanged t -> let uu____3656 = f t  in Unchanged uu____3656
      | Simplified (t,gs) ->
          let uu____3663 = let uu____3670 = f t  in (uu____3670, gs)  in
          Simplified uu____3663
      | Dual (tn,tp,gs) ->
          let uu____3680 =
            let uu____3689 = f tn  in
            let uu____3690 = f tp  in (uu____3689, uu____3690, gs)  in
          Dual uu____3680
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3744 = f t1 t2  in Unchanged uu____3744
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3756 = let uu____3763 = f t1 t2  in (uu____3763, gs)
               in
            Simplified uu____3756
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3777 = let uu____3784 = f t1 t2  in (uu____3784, gs)
               in
            Simplified uu____3777
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3803 =
              let uu____3810 = f t1 t2  in
              (uu____3810, (FStar_List.append gs1 gs2))  in
            Simplified uu____3803
        | uu____3813 ->
            let uu____3822 = explode x  in
            (match uu____3822 with
             | (n1,p1,gs1) ->
                 let uu____3840 = explode y  in
                 (match uu____3840 with
                  | (n2,p2,gs2) ->
                      let uu____3858 =
                        let uu____3867 = f n1 n2  in
                        let uu____3868 = f p1 p2  in
                        (uu____3867, uu____3868, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3858))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3933 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3933
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3976  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____4010 =
              let uu____4011 = FStar_Syntax_Subst.compress t  in
              uu____4011.FStar_Syntax_Syntax.n  in
            match uu____4010 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____4023 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____4023 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____4047 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____4047 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4065;
                   FStar_Syntax_Syntax.vars = uu____4066;_},(p,uu____4068)::
                 (q,uu____4070)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____4110 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4110
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____4113 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____4113 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____4119 = FStar_Syntax_Util.mk_imp l r  in
                       uu____4119.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____4123;
                   FStar_Syntax_Syntax.vars = uu____4124;_},(p,uu____4126)::
                 (q,uu____4128)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____4168 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4168
                   in
                let xq =
                  let uu____4170 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4170
                   in
                let r1 =
                  let uu____4172 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4172 p  in
                let r2 =
                  let uu____4174 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4174 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4177,Unchanged uu____4178) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4188 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4188.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4191 ->
                     let uu____4196 = explode r1  in
                     (match uu____4196 with
                      | (pn,pp,gs1) ->
                          let uu____4214 = explode r2  in
                          (match uu____4214 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4235 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4236 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4235
                                   uu____4236
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4288  ->
                       fun r  ->
                         match uu____4288 with
                         | (a,q) ->
                             let r' = traverse f pol e a  in
                             comb2
                               (fun a1  -> fun args1  -> (a1, q) :: args1) r'
                               r) args (tpure [])
                   in
                comb2
                  (fun hd2  ->
                     fun args1  -> FStar_Syntax_Syntax.Tm_app (hd2, args1))
                  r0 r1
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____4406 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4406 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4440  ->
                            match uu____4440 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4454 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___61_4478 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___61_4478.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___61_4478.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4454 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4498 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4498.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4544 = traverse f pol e t1  in
                let uu____4549 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4549 uu____4544
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___62_4587 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___62_4587.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___62_4587.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4594 =
                f pol e
                  (let uu___63_4598 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___63_4598.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___63_4598.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4594
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___64_4608 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___64_4608.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___64_4608.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4609 = explode rp  in
              (match uu____4609 with
               | (uu____4618,p',gs') ->
                   Dual
                     ((let uu___65_4632 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___65_4632.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___65_4632.FStar_Syntax_Syntax.vars)
                       }), p', (FStar_List.append gs gs')))
  
let (getprop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant] e t
         in
      FStar_Syntax_Util.un_squash tn
  
let (preprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.term,FStar_Options.optionstate)
        FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun env  ->
    fun goal  ->
      (let uu____4667 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4667);
      (let uu____4688 = FStar_ST.op_Bang tacdbg  in
       if uu____4688
       then
         let uu____4708 =
           let uu____4709 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4709
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4710 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4708
           uu____4710
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4739 =
         let uu____4746 = traverse by_tactic_interp Pos env goal  in
         match uu____4746 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4764 -> failwith "no"  in
       match uu____4739 with
       | (t',gs) ->
           ((let uu____4786 = FStar_ST.op_Bang tacdbg  in
             if uu____4786
             then
               let uu____4806 =
                 let uu____4807 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4807
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4808 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4806 uu____4808
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4855  ->
                    fun g  ->
                      match uu____4855 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4900 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____4900 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4903 =
                                  let uu____4904 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty
                                     in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4904
                                   in
                                failwith uu____4903
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4907 = FStar_ST.op_Bang tacdbg  in
                            if uu____4907
                            then
                              let uu____4927 = FStar_Util.string_of_int n1
                                 in
                              let uu____4928 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4927 uu____4928
                            else ());
                           (let gt' =
                              let uu____4931 =
                                let uu____4932 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4932
                                 in
                              FStar_TypeChecker_Util.label uu____4931
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____4947 = s1  in
             match uu____4947 with
             | (uu____4968,gs1) ->
                 let uu____4986 =
                   let uu____4993 = FStar_Options.peek ()  in
                   (env, t', uu____4993)  in
                 uu____4986 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____5004 =
        let uu____5005 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____5005  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____5004 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____5006 =
      let uu____5007 =
        let uu____5008 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____5009 =
          let uu____5012 = FStar_Syntax_Syntax.as_arg a  in [uu____5012]  in
        uu____5008 :: uu____5009  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____5007  in
    uu____5006 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____5025 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____5025);
        (let uu____5045 =
           let uu____5052 = reify_tactic tau  in
           run_tactic_on_typ uu____5052 env typ  in
         match uu____5045 with
         | (gs,w) ->
             let uu____5059 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5063 =
                      let uu____5064 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5064  in
                    Prims.op_Negation uu____5063) gs
                in
             if uu____5059
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                   "synthesis left open goals") typ.FStar_Syntax_Syntax.pos
             else w)
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun tau  ->
      (let uu____5079 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____5079);
      (let typ = FStar_Reflection_Data.fstar_refl_decls  in
       let uu____5100 =
         let uu____5107 = reify_tactic tau  in
         run_tactic_on_typ uu____5107 env typ  in
       match uu____5100 with
       | (gs,w) ->
           ((let uu____5117 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____5121 =
                      let uu____5122 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____5122  in
                    Prims.op_Negation uu____5121) gs
                in
             if uu____5117
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                   "splice left open goals") typ.FStar_Syntax_Syntax.pos
             else ());
            (let w1 =
               FStar_TypeChecker_Normalize.normalize
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.UnfoldUntil
                   FStar_Syntax_Syntax.Delta_constant;
                 FStar_TypeChecker_Normalize.Primops;
                 FStar_TypeChecker_Normalize.Unascribe;
                 FStar_TypeChecker_Normalize.Unmeta] env w
                in
             let uu____5127 =
               let uu____5132 =
                 FStar_Syntax_Embeddings.unembed_list
                   FStar_Reflection_Embeddings.unembed_sigelt
                  in
               uu____5132 w1  in
             FStar_All.pipe_left FStar_Util.must uu____5127)))
  