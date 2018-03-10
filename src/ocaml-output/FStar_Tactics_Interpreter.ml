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
  fun uu____1242  ->
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
    let decr_depth_interp psc args =
      match args with
      | (ps,uu____1730)::[] ->
          let uu____1747 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1747
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1755 =
                 let uu____1756 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1757 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1756
                   uu____1757
                  in
               FStar_Pervasives_Native.Some uu____1755)
      | uu____1758 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____1762 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1762;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____1775)::[] ->
          let uu____1792 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1792
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1800 =
                 let uu____1801 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1802 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1801
                   uu____1802
                  in
               FStar_Pervasives_Native.Some uu____1800)
      | uu____1803 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____1807 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1807;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____1824)::[] ->
          let uu____1841 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1841
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1854 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____1871)::(r,uu____1873)::[] ->
          let uu____1900 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1900
            (fun ps1  ->
               let uu____1906 = FStar_Syntax_Embeddings.unembed_range r  in
               FStar_Util.bind_opt uu____1906
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____1914 =
                      let uu____1915 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Tactics_Embedding.embed_proofstate uu____1915 ps'
                       in
                    FStar_Pervasives_Native.Some uu____1914))
      | uu____1916 ->
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
      let uu___58_1930 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___58_1930.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___58_1930.FStar_Syntax_Syntax.vars)
      }  in
    let get1 t = FStar_Pervasives_Native.Some t  in
    let uu____1937 =
      let uu____1940 =
        mktac2 () () () "__fail"
          (fun a438  ->
             fun a439  ->
               (Obj.magic (fun uu____1942  -> FStar_Tactics_Basic.fail)) a438
                 a439) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit
         in
      let uu____1943 =
        let uu____1946 =
          mktac0 () "__trivial" (Obj.magic FStar_Tactics_Basic.trivial)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit
           in
        let uu____1947 =
          let uu____1950 =
            let uu____1951 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit
               in
            mktac2 () () () "__trytac"
              (fun a440  ->
                 fun a441  ->
                   (Obj.magic (fun uu____1957  -> FStar_Tactics_Basic.trytac))
                     a440 a441) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____1951)
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1964 =
            let uu____1967 =
              mktac0 () "__intro" (Obj.magic FStar_Tactics_Basic.intro)
                (Obj.magic FStar_Reflection_Embeddings.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder
               in
            let uu____1968 =
              let uu____1971 =
                let uu____1972 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                let uu____1979 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                mktac0 () "__intro_rec"
                  (Obj.magic FStar_Tactics_Basic.intro_rec)
                  (Obj.magic uu____1972) uu____1979
                 in
              let uu____1986 =
                let uu____1989 =
                  let uu____1990 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step
                     in
                  mktac1 () () "__norm"
                    (fun a442  -> (Obj.magic FStar_Tactics_Basic.norm) a442)
                    (Obj.magic uu____1990)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit
                   in
                let uu____1999 =
                  let uu____2002 =
                    let uu____2003 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step
                       in
                    mktac3 () () () () "__norm_term_env"
                      (fun a443  ->
                         fun a444  ->
                           fun a445  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a443 a444 a445)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_env)
                      (Obj.magic uu____2003)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_term)
                      (Obj.magic FStar_Reflection_Embeddings.embed_term)
                      FStar_Syntax_Syntax.t_term
                     in
                  let uu____2012 =
                    let uu____2015 =
                      let uu____2016 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step
                         in
                      mktac2 () () () "__norm_binder_type"
                        (fun a446  ->
                           fun a447  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a446 a447) (Obj.magic uu____2016)
                        (Obj.magic FStar_Reflection_Embeddings.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2025 =
                      let uu____2028 =
                        mktac2 () () () "__rename_to"
                          (fun a448  ->
                             fun a449  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a448
                                 a449)
                          (Obj.magic
                             FStar_Reflection_Embeddings.unembed_binder)
                          (Obj.magic FStar_Syntax_Embeddings.unembed_string)
                          (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                          FStar_Syntax_Syntax.t_unit
                         in
                      let uu____2029 =
                        let uu____2032 =
                          mktac1 () () "__binder_retype"
                            (fun a450  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a450)
                            (Obj.magic
                               FStar_Reflection_Embeddings.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit
                           in
                        let uu____2033 =
                          let uu____2036 =
                            mktac0 () "__revert"
                              (Obj.magic FStar_Tactics_Basic.revert)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit
                             in
                          let uu____2037 =
                            let uu____2040 =
                              mktac0 () "__clear_top"
                                (Obj.magic FStar_Tactics_Basic.clear_top)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit
                               in
                            let uu____2041 =
                              let uu____2044 =
                                mktac1 () () "__clear"
                                  (fun a451  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a451)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.unembed_binder)
                                  (Obj.magic
                                     FStar_Syntax_Embeddings.embed_unit)
                                  FStar_Syntax_Syntax.t_unit
                                 in
                              let uu____2045 =
                                let uu____2048 =
                                  mktac1 () () "__rewrite"
                                    (fun a452  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a452)
                                    (Obj.magic
                                       FStar_Reflection_Embeddings.unembed_binder)
                                    (Obj.magic
                                       FStar_Syntax_Embeddings.embed_unit)
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                let uu____2049 =
                                  let uu____2052 =
                                    mktac0 () "__smt"
                                      (Obj.magic FStar_Tactics_Basic.smt)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit
                                     in
                                  let uu____2053 =
                                    let uu____2056 =
                                      mktac0 () "__refine_intro"
                                        (Obj.magic
                                           FStar_Tactics_Basic.refine_intro)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit
                                       in
                                    let uu____2057 =
                                      let uu____2060 =
                                        mktac3 () () () () "__t_exact"
                                          (fun a453  ->
                                             fun a454  ->
                                               fun a455  ->
                                                 (Obj.magic
                                                    FStar_Tactics_Basic.t_exact)
                                                   a453 a454 a455)
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
                                      let uu____2061 =
                                        let uu____2064 =
                                          mktac1 () () "__apply"
                                            (fun a456  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a456)
                                            (Obj.magic
                                               FStar_Reflection_Embeddings.unembed_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_unit)
                                            FStar_Syntax_Syntax.t_unit
                                           in
                                        let uu____2065 =
                                          let uu____2068 =
                                            mktac1 () () "__apply_raw"
                                              (fun a457  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a457)
                                              (Obj.magic
                                                 FStar_Reflection_Embeddings.unembed_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.embed_unit)
                                              FStar_Syntax_Syntax.t_unit
                                             in
                                          let uu____2069 =
                                            let uu____2072 =
                                              mktac1 () () "__apply_lemma"
                                                (fun a458  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a458)
                                                (Obj.magic
                                                   FStar_Reflection_Embeddings.unembed_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.embed_unit)
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            let uu____2073 =
                                              let uu____2076 =
                                                let uu____2077 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a459  ->
                                                     fun a460  ->
                                                       fun a461  ->
                                                         fun a462  ->
                                                           fun a463  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2086
                                                                    ->
                                                                   fun
                                                                    uu____2087
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a459 a460 a461
                                                               a462 a463)
                                                  (Obj.magic get1)
                                                  (Obj.magic get1)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.unembed_int)
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic uu____2077)
                                                  FStar_Syntax_Syntax.t_unit
                                                 in
                                              let uu____2094 =
                                                let uu____2097 =
                                                  mktac1 () ()
                                                    "__set_options"
                                                    (fun a464  ->
                                                       (Obj.magic
                                                          FStar_Tactics_Basic.set_options)
                                                         a464)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.unembed_string)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.embed_unit)
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                let uu____2098 =
                                                  let uu____2101 =
                                                    mktac2 () () () "__seq"
                                                      (fun a465  ->
                                                         fun a466  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.seq)
                                                             a465 a466)
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
                                                  let uu____2102 =
                                                    let uu____2105 =
                                                      mktac1 () () "__tc"
                                                        (fun a467  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a467)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.unembed_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.embed_term)
                                                        FStar_Syntax_Syntax.t_term
                                                       in
                                                    let uu____2106 =
                                                      let uu____2109 =
                                                        mktac1 () ()
                                                          "__unshelve"
                                                          (fun a468  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a468)
                                                          (Obj.magic
                                                             FStar_Reflection_Embeddings.unembed_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.embed_unit)
                                                          FStar_Syntax_Syntax.t_unit
                                                         in
                                                      let uu____2110 =
                                                        let uu____2113 =
                                                          mktac2 () () ()
                                                            "__unquote"
                                                            (fun a469  ->
                                                               fun a470  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a469 a470)
                                                            (Obj.magic get1)
                                                            (Obj.magic
                                                               FStar_Reflection_Embeddings.unembed_term)
                                                            (Obj.magic put1)
                                                            FStar_Syntax_Syntax.t_unit
                                                           in
                                                        let uu____2114 =
                                                          let uu____2117 =
                                                            mktac1 () ()
                                                              "__prune"
                                                              (fun a471  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a471)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.unembed_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.embed_unit)
                                                              FStar_Syntax_Syntax.t_unit
                                                             in
                                                          let uu____2118 =
                                                            let uu____2121 =
                                                              mktac1 () ()
                                                                "__addns"
                                                                (fun a472  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a472)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.embed_unit)
                                                                FStar_Syntax_Syntax.t_unit
                                                               in
                                                            let uu____2122 =
                                                              let uu____2125
                                                                =
                                                                mktac1 () ()
                                                                  "__print"
                                                                  (fun a473 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun x 
                                                                    ->
                                                                    FStar_Tactics_Basic.tacprint
                                                                    x;
                                                                    FStar_Tactics_Basic.ret
                                                                    ())) a473)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                  FStar_Syntax_Syntax.t_unit
                                                                 in
                                                              let uu____2130
                                                                =
                                                                let uu____2133
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "__dump"
                                                                    (
                                                                    fun a474 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a474)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                   in
                                                                let uu____2134
                                                                  =
                                                                  let uu____2137
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__dump1"
                                                                    (fun a475
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a475)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                  let uu____2138
                                                                    =
                                                                    let uu____2141
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a476
                                                                     ->
                                                                    fun a477 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a476 a477)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_direction)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2142
                                                                    =
                                                                    let uu____2145
                                                                    =
                                                                    let uu____2146
                                                                    =
                                                                    let uu____2157
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_pair
                                                                    FStar_Syntax_Embeddings.unembed_bool
                                                                    FStar_Syntax_Embeddings.unembed_int
                                                                     in
                                                                    unembed_tactic_1
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    uu____2157
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__topdown_rewrite"
                                                                    (fun a478
                                                                     ->
                                                                    fun a479 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.topdown_rewrite)
                                                                    a478 a479)
                                                                    (Obj.magic
                                                                    uu____2146)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2176
                                                                    =
                                                                    let uu____2179
                                                                    =
                                                                    mktac0 ()
                                                                    "__trefl"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2180
                                                                    =
                                                                    let uu____2183
                                                                    =
                                                                    mktac0 ()
                                                                    "__later"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2184
                                                                    =
                                                                    let uu____2187
                                                                    =
                                                                    mktac0 ()
                                                                    "__dup"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2188
                                                                    =
                                                                    let uu____2191
                                                                    =
                                                                    mktac0 ()
                                                                    "__flip"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2192
                                                                    =
                                                                    let uu____2195
                                                                    =
                                                                    mktac0 ()
                                                                    "__qed"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2196
                                                                    =
                                                                    let uu____2199
                                                                    =
                                                                    let uu____2200
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2207
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "__cases"
                                                                    (fun a480
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a480)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    uu____2200)
                                                                    uu____2207
                                                                     in
                                                                    let uu____2214
                                                                    =
                                                                    let uu____2217
                                                                    =
                                                                    mktac0 ()
                                                                    "__top_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2218
                                                                    =
                                                                    let uu____2221
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2222
                                                                    =
                                                                    let uu____2225
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_goal"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2226
                                                                    =
                                                                    let uu____2229
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_witness"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2230
                                                                    =
                                                                    let uu____2233
                                                                    =
                                                                    mktac0 ()
                                                                    "__is_guard"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2234
                                                                    =
                                                                    let uu____2237
                                                                    =
                                                                    let uu____2238
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Embeddings.unembed_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__uvar_env"
                                                                    (fun a481
                                                                     ->
                                                                    fun a482 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a481 a482)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_env)
                                                                    (Obj.magic
                                                                    uu____2238)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2247
                                                                    =
                                                                    let uu____2250
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__unify"
                                                                    (fun a483
                                                                     ->
                                                                    fun a484 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a483 a484)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2251
                                                                    =
                                                                    let uu____2254
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "__launch_process"
                                                                    (fun a485
                                                                     ->
                                                                    fun a486 
                                                                    ->
                                                                    fun a487 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a485 a486
                                                                    a487)
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
                                                                    let uu____2255
                                                                    =
                                                                    let uu____2258
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__fresh_bv_named"
                                                                    (fun a488
                                                                     ->
                                                                    fun a489 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh_bv_named)
                                                                    a488 a489)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_bv)
                                                                    FStar_Syntax_Syntax.t_bv
                                                                     in
                                                                    [uu____2258;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step]
                                                                     in
                                                                    uu____2254
                                                                    ::
                                                                    uu____2255
                                                                     in
                                                                    uu____2250
                                                                    ::
                                                                    uu____2251
                                                                     in
                                                                    uu____2237
                                                                    ::
                                                                    uu____2247
                                                                     in
                                                                    uu____2233
                                                                    ::
                                                                    uu____2234
                                                                     in
                                                                    uu____2229
                                                                    ::
                                                                    uu____2230
                                                                     in
                                                                    uu____2225
                                                                    ::
                                                                    uu____2226
                                                                     in
                                                                    uu____2221
                                                                    ::
                                                                    uu____2222
                                                                     in
                                                                    uu____2217
                                                                    ::
                                                                    uu____2218
                                                                     in
                                                                    uu____2199
                                                                    ::
                                                                    uu____2214
                                                                     in
                                                                    uu____2195
                                                                    ::
                                                                    uu____2196
                                                                     in
                                                                    uu____2191
                                                                    ::
                                                                    uu____2192
                                                                     in
                                                                    uu____2187
                                                                    ::
                                                                    uu____2188
                                                                     in
                                                                    uu____2183
                                                                    ::
                                                                    uu____2184
                                                                     in
                                                                    uu____2179
                                                                    ::
                                                                    uu____2180
                                                                     in
                                                                    uu____2145
                                                                    ::
                                                                    uu____2176
                                                                     in
                                                                    uu____2141
                                                                    ::
                                                                    uu____2142
                                                                     in
                                                                  uu____2137
                                                                    ::
                                                                    uu____2138
                                                                   in
                                                                uu____2133 ::
                                                                  uu____2134
                                                                 in
                                                              uu____2125 ::
                                                                uu____2130
                                                               in
                                                            uu____2121 ::
                                                              uu____2122
                                                             in
                                                          uu____2117 ::
                                                            uu____2118
                                                           in
                                                        uu____2113 ::
                                                          uu____2114
                                                         in
                                                      uu____2109 ::
                                                        uu____2110
                                                       in
                                                    uu____2105 :: uu____2106
                                                     in
                                                  uu____2101 :: uu____2102
                                                   in
                                                uu____2097 :: uu____2098  in
                                              uu____2076 :: uu____2094  in
                                            uu____2072 :: uu____2073  in
                                          uu____2068 :: uu____2069  in
                                        uu____2064 :: uu____2065  in
                                      uu____2060 :: uu____2061  in
                                    uu____2056 :: uu____2057  in
                                  uu____2052 :: uu____2053  in
                                uu____2048 :: uu____2049  in
                              uu____2044 :: uu____2045  in
                            uu____2040 :: uu____2041  in
                          uu____2036 :: uu____2037  in
                        uu____2032 :: uu____2033  in
                      uu____2028 :: uu____2029  in
                    uu____2015 :: uu____2025  in
                  uu____2002 :: uu____2012  in
                uu____1989 :: uu____1999  in
              uu____1971 :: uu____1986  in
            uu____1967 :: uu____1968  in
          uu____1950 :: uu____1964  in
        uu____1946 :: uu____1947  in
      uu____1940 :: uu____1943  in
    FStar_List.append uu____1937
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)

and unembed_tactic_1 :
  'Aa 'Ab .
    'Aa FStar_Syntax_Embeddings.embedder ->
      'Ab FStar_Syntax_Embeddings.unembedder ->
        FStar_Syntax_Syntax.term ->
          ('Aa -> 'Ab FStar_Tactics_Basic.tac) FStar_Pervasives_Native.option
  =
  fun arg  ->
    fun res  ->
      fun f  ->
        FStar_Pervasives_Native.Some
          (fun x  ->
             let rng = FStar_Range.dummyRange  in
             let x_tm = arg rng x  in
             let app =
               let uu____2288 =
                 let uu____2289 =
                   let uu____2290 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____2290]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____2289  in
               uu____2288 FStar_Pervasives_Native.None rng  in
             unembed_tactic_0 res app)

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
             let uu____2319 =
               let uu____2320 =
                 let uu____2321 =
                   let uu____2322 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____2322  in
                 [uu____2321]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2320  in
             uu____2319 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____2329 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____2329
            then
              let uu____2330 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2330
            else ());
           (let result =
              let uu____2333 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2333 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____2337 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____2337
             then
               let uu____2338 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2338
             else ());
            (let res =
               FStar_Tactics_Embedding.unembed_result result unembed_b  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2383 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2383
                   (fun uu____2387  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2410 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2410
                   (fun uu____2414  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2427 =
                   let uu____2432 =
                     let uu____2433 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2433
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2432)  in
                 FStar_Errors.raise_error uu____2427
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2442 = unembed_tactic_0 unembed_b embedded_tac_b  in
      FStar_All.pipe_left (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
        uu____2442

let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2498  ->
             match uu____2498 with
             | (r,uu____2518,uv,uu____2520,ty,rng) ->
                 let uu____2523 =
                   let uu____2524 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____2525 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2524 uu____2525 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____2523, rng)) is
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
        (let uu____2574 = FStar_ST.op_Bang tacdbg  in
         if uu____2574
         then
           let uu____2594 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2594
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         (let uu____2598 = FStar_ST.op_Bang tacdbg  in
          if uu____2598
          then
            let uu____2618 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____2618
          else ());
         (let uu____2620 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
          match uu____2620 with
          | (uu____2633,uu____2634,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic1
                   in
                let uu____2641 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                match uu____2641 with
                | (env1,uu____2655) ->
                    let env2 =
                      let uu___59_2661 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___59_2661.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___59_2661.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___59_2661.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___59_2661.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___59_2661.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___59_2661.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___59_2661.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___59_2661.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___59_2661.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___59_2661.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___59_2661.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___59_2661.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___59_2661.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___59_2661.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___59_2661.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___59_2661.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___59_2661.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___59_2661.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___59_2661.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___59_2661.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___59_2661.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___59_2661.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___59_2661.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___59_2661.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___59_2661.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___59_2661.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___59_2661.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___59_2661.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth =
                          (uu___59_2661.FStar_TypeChecker_Env.synth);
                        FStar_TypeChecker_Env.splice =
                          (uu___59_2661.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___59_2661.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___59_2661.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___59_2661.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___59_2661.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___59_2661.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let uu____2662 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ  in
                    (match uu____2662 with
                     | (ps,w) ->
                         ((let uu____2676 = FStar_ST.op_Bang tacdbg  in
                           if uu____2676
                           then
                             let uu____2696 =
                               FStar_Syntax_Print.term_to_string typ  in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____2696
                           else ());
                          (let uu____2698 =
                             FStar_Util.record_time
                               (fun uu____2708  ->
                                  FStar_Tactics_Basic.run tau ps)
                              in
                           match uu____2698 with
                           | (res,ms) ->
                               ((let uu____2722 = FStar_ST.op_Bang tacdbg  in
                                 if uu____2722
                                 then
                                   let uu____2742 =
                                     FStar_Util.string_of_int ms  in
                                   FStar_Util.print1
                                     "Tactic ran in %s milliseconds\n"
                                     uu____2742
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____2750,ps1) ->
                                     ((let uu____2753 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____2753
                                       then
                                         let uu____2773 =
                                           FStar_Syntax_Print.term_to_string
                                             w
                                            in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____2773
                                       else ());
                                      FStar_List.iter
                                        (fun g1  ->
                                           let uu____2780 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____2780
                                           then
                                             let uu____2781 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____2781
                                              then ()
                                              else
                                                (let uu____2783 =
                                                   let uu____2784 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____2784
                                                    in
                                                 failwith uu____2783))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___60_2787 =
                                           FStar_TypeChecker_Rel.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___60_2787.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___60_2787.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___60_2787.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         let uu____2789 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env2 g1
                                            in
                                         FStar_All.pipe_right uu____2789
                                           FStar_TypeChecker_Rel.resolve_implicits_tac
                                          in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s,ps1) ->
                                     ((let uu____2796 =
                                         let uu____2797 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____2797 ps1
                                          in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____2796 "at the time of failure");
                                      (let uu____2798 =
                                         let uu____2803 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s
                                            in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____2803)
                                          in
                                       FStar_Errors.raise_error uu____2798
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2813 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2817 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2821 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2870 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2906 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2956 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____2994 . 'Auu____2994 -> 'Auu____2994 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3013 = FStar_Syntax_Util.head_and_args t  in
        match uu____3013 with
        | (hd1,args) ->
            let uu____3050 =
              let uu____3063 =
                let uu____3064 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3064.FStar_Syntax_Syntax.n  in
              (uu____3063, args)  in
            (match uu____3050 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3077))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3140 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3140 with
                       | (gs,uu____3148) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3155 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3155 with
                       | (gs,uu____3163) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3214 =
                        let uu____3221 =
                          let uu____3224 =
                            let uu____3225 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3225
                             in
                          [uu____3224]  in
                        (FStar_Syntax_Util.t_true, uu____3221)  in
                      Simplified uu____3214
                  | Both  ->
                      let uu____3236 =
                        let uu____3249 =
                          let uu____3252 =
                            let uu____3253 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3253
                             in
                          [uu____3252]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3249)  in
                      Dual uu____3236
                  | Neg  -> Simplified (assertion, []))
             | uu____3274 -> Unchanged t)
  
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
    fun uu___57_3354  ->
      match uu___57_3354 with
      | Unchanged t -> let uu____3360 = f t  in Unchanged uu____3360
      | Simplified (t,gs) ->
          let uu____3367 = let uu____3374 = f t  in (uu____3374, gs)  in
          Simplified uu____3367
      | Dual (tn,tp,gs) ->
          let uu____3384 =
            let uu____3393 = f tn  in
            let uu____3394 = f tp  in (uu____3393, uu____3394, gs)  in
          Dual uu____3384
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3448 = f t1 t2  in Unchanged uu____3448
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3460 = let uu____3467 = f t1 t2  in (uu____3467, gs)
               in
            Simplified uu____3460
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3481 = let uu____3488 = f t1 t2  in (uu____3488, gs)
               in
            Simplified uu____3481
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3507 =
              let uu____3514 = f t1 t2  in
              (uu____3514, (FStar_List.append gs1 gs2))  in
            Simplified uu____3507
        | uu____3517 ->
            let uu____3526 = explode x  in
            (match uu____3526 with
             | (n1,p1,gs1) ->
                 let uu____3544 = explode y  in
                 (match uu____3544 with
                  | (n2,p2,gs2) ->
                      let uu____3562 =
                        let uu____3571 = f n1 n2  in
                        let uu____3572 = f p1 p2  in
                        (uu____3571, uu____3572, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3562))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3637 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3637
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3680  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3714 =
              let uu____3715 = FStar_Syntax_Subst.compress t  in
              uu____3715.FStar_Syntax_Syntax.n  in
            match uu____3714 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3727 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3727 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3751 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3751 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3769;
                   FStar_Syntax_Syntax.vars = uu____3770;_},(p,uu____3772)::
                 (q,uu____3774)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3814 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3814
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3817 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3817 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3823 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3823.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3827;
                   FStar_Syntax_Syntax.vars = uu____3828;_},(p,uu____3830)::
                 (q,uu____3832)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3872 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3872
                   in
                let xq =
                  let uu____3874 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3874
                   in
                let r1 =
                  let uu____3876 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3876 p  in
                let r2 =
                  let uu____3878 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3878 q  in
                (match (r1, r2) with
                 | (Unchanged uu____3881,Unchanged uu____3882) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3892 = FStar_Syntax_Util.mk_iff l r  in
                            uu____3892.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3895 ->
                     let uu____3900 = explode r1  in
                     (match uu____3900 with
                      | (pn,pp,gs1) ->
                          let uu____3918 = explode r2  in
                          (match uu____3918 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3939 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____3940 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____3939
                                   uu____3940
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____3992  ->
                       fun r  ->
                         match uu____3992 with
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
                let uu____4110 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4110 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4144  ->
                            match uu____4144 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4158 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___61_4182 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___61_4182.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___61_4182.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4158 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4202 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4202.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4248 = traverse f pol e t1  in
                let uu____4253 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4253 uu____4248
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___62_4291 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___62_4291.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___62_4291.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4298 =
                f pol e
                  (let uu___63_4302 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___63_4302.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___63_4302.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4298
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___64_4312 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___64_4312.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___64_4312.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4313 = explode rp  in
              (match uu____4313 with
               | (uu____4322,p',gs') ->
                   Dual
                     ((let uu___65_4336 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___65_4336.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___65_4336.FStar_Syntax_Syntax.vars)
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
      (let uu____4371 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4371);
      (let uu____4392 = FStar_ST.op_Bang tacdbg  in
       if uu____4392
       then
         let uu____4412 =
           let uu____4413 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4413
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4414 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4412
           uu____4414
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4443 =
         let uu____4450 = traverse by_tactic_interp Pos env goal  in
         match uu____4450 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4468 -> failwith "no"  in
       match uu____4443 with
       | (t',gs) ->
           ((let uu____4490 = FStar_ST.op_Bang tacdbg  in
             if uu____4490
             then
               let uu____4510 =
                 let uu____4511 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4511
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4512 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4510 uu____4512
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4559  ->
                    fun g  ->
                      match uu____4559 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4604 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____4604 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4607 =
                                  let uu____4608 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty
                                     in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4608
                                   in
                                failwith uu____4607
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4611 = FStar_ST.op_Bang tacdbg  in
                            if uu____4611
                            then
                              let uu____4631 = FStar_Util.string_of_int n1
                                 in
                              let uu____4632 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4631 uu____4632
                            else ());
                           (let gt' =
                              let uu____4635 =
                                let uu____4636 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4636
                                 in
                              FStar_TypeChecker_Util.label uu____4635
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____4651 = s1  in
             match uu____4651 with
             | (uu____4672,gs1) ->
                 let uu____4690 =
                   let uu____4697 = FStar_Options.peek ()  in
                   (env, t', uu____4697)  in
                 uu____4690 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4708 =
        let uu____4709 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4709  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4708 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4710 =
      let uu____4711 =
        let uu____4712 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4713 =
          let uu____4716 = FStar_Syntax_Syntax.as_arg a  in [uu____4716]  in
        uu____4712 :: uu____4713  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4711  in
    uu____4710 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4729 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____4729);
        (let uu____4749 =
           let uu____4756 = reify_tactic tau  in
           run_tactic_on_typ uu____4756 env typ  in
         match uu____4749 with
         | (gs,w) ->
             let uu____4763 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4767 =
                      let uu____4768 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____4768  in
                    Prims.op_Negation uu____4767) gs
                in
             if uu____4763
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
      (let uu____4783 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4783);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____4804 =
         let uu____4811 = reify_tactic tau  in
         run_tactic_on_typ uu____4811 env typ  in
       match uu____4804 with
       | (gs,w) ->
           ((let uu____4821 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4825 =
                      let uu____4826 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____4826  in
                    Prims.op_Negation uu____4825) gs
                in
             if uu____4821
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
             let uu____4831 =
               let uu____4836 =
                 FStar_Syntax_Embeddings.unembed_list
                   FStar_Reflection_Embeddings.unembed_sigelt
                  in
               uu____4836 w1  in
             FStar_All.pipe_left FStar_Util.must uu____4831)))
  