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
              | (embedded_state,uu____89)::[] ->
                  let uu____106 =
                    FStar_Tactics_Embedding.unembed_proofstate embedded_state
                     in
                  FStar_Util.bind_opt uu____106
                    (fun ps  ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                       FStar_Tactics_Basic.log ps1
                         (fun uu____120  ->
                            let uu____121 = FStar_Ident.string_of_lid nm  in
                            let uu____122 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.print2 "Reached %s, args are: %s\n"
                              uu____121 uu____122);
                       (let res = FStar_Tactics_Basic.run t ps1  in
                        let uu____126 =
                          let uu____127 =
                            FStar_TypeChecker_Normalize.psc_range psc  in
                          let uu____128 =
                            FStar_Tactics_Embedding.embed_result embed_r t_r
                             in
                          uu____128 uu____127 res  in
                        FStar_Pervasives_Native.Some uu____126))
              | uu____142 ->
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
                | (a,uu____214)::(embedded_state,uu____216)::[] ->
                    let uu____243 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state
                       in
                    FStar_Util.bind_opt uu____243
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____256  ->
                              let uu____257 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____258 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____257 uu____258);
                         (let uu____259 = unembed_a a  in
                          FStar_Util.bind_opt uu____259
                            (fun a1  ->
                               let res =
                                 let uu____271 = t a1  in
                                 FStar_Tactics_Basic.run uu____271 ps1  in
                               let uu____274 =
                                 let uu____275 =
                                   FStar_TypeChecker_Normalize.psc_range psc
                                    in
                                 let uu____276 =
                                   FStar_Tactics_Embedding.embed_result
                                     embed_r t_r
                                    in
                                 uu____276 uu____275 res  in
                               FStar_Pervasives_Native.Some uu____274)))
                | uu____290 ->
                    let uu____291 =
                      let uu____292 = FStar_Ident.string_of_lid nm  in
                      let uu____293 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____292 uu____293
                       in
                    failwith uu____291
  
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
                | (a,uu____370)::(embedded_state,uu____372)::[] ->
                    let uu____399 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state
                       in
                    FStar_Util.bind_opt uu____399
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____412  ->
                              let uu____413 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____414 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state
                                 in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____413 uu____414);
                         (let uu____415 = unembed_a a  in
                          FStar_Util.bind_opt uu____415
                            (fun a1  ->
                               let res =
                                 let uu____427 = t psc a1  in
                                 FStar_Tactics_Basic.run uu____427 ps1  in
                               let uu____430 =
                                 let uu____431 =
                                   FStar_TypeChecker_Normalize.psc_range psc
                                    in
                                 let uu____432 =
                                   FStar_Tactics_Embedding.embed_result
                                     embed_r t_r
                                    in
                                 uu____432 uu____431 res  in
                               FStar_Pervasives_Native.Some uu____430)))
                | uu____446 ->
                    let uu____447 =
                      let uu____448 = FStar_Ident.string_of_lid nm  in
                      let uu____449 = FStar_Syntax_Print.args_to_string args
                         in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____448 uu____449
                       in
                    failwith uu____447
  
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
                  | (a,uu____541)::(b,uu____543)::(embedded_state,uu____545)::[]
                      ->
                      let uu____582 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state
                         in
                      FStar_Util.bind_opt uu____582
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____595  ->
                                let uu____596 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____597 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____596
                                  uu____597);
                           (let uu____598 = unembed_a a  in
                            FStar_Util.bind_opt uu____598
                              (fun a1  ->
                                 let uu____606 = unembed_b b  in
                                 FStar_Util.bind_opt uu____606
                                   (fun b1  ->
                                      let res =
                                        let uu____618 = t a1 b1  in
                                        FStar_Tactics_Basic.run uu____618 ps1
                                         in
                                      let uu____621 =
                                        let uu____622 =
                                          FStar_TypeChecker_Normalize.psc_range
                                            psc
                                           in
                                        let uu____623 =
                                          FStar_Tactics_Embedding.embed_result
                                            embed_r t_r
                                           in
                                        uu____623 uu____622 res  in
                                      FStar_Pervasives_Native.Some uu____621))))
                  | uu____637 ->
                      let uu____638 =
                        let uu____639 = FStar_Ident.string_of_lid nm  in
                        let uu____640 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____639 uu____640
                         in
                      failwith uu____638
  
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
                    | (a,uu____752)::(b,uu____754)::(c,uu____756)::(embedded_state,uu____758)::[]
                        ->
                        let uu____805 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state
                           in
                        FStar_Util.bind_opt uu____805
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____818  ->
                                  let uu____819 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____820 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state
                                     in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____819
                                    uu____820);
                             (let uu____821 = unembed_a a  in
                              FStar_Util.bind_opt uu____821
                                (fun a1  ->
                                   let uu____829 = unembed_b b  in
                                   FStar_Util.bind_opt uu____829
                                     (fun b1  ->
                                        let uu____837 = unembed_c c  in
                                        FStar_Util.bind_opt uu____837
                                          (fun c1  ->
                                             let res =
                                               let uu____849 = t a1 b1 c1  in
                                               FStar_Tactics_Basic.run
                                                 uu____849 ps1
                                                in
                                             let uu____852 =
                                               let uu____853 =
                                                 FStar_TypeChecker_Normalize.psc_range
                                                   psc
                                                  in
                                               let uu____854 =
                                                 FStar_Tactics_Embedding.embed_result
                                                   embed_r t_r
                                                  in
                                               uu____854 uu____853 res  in
                                             FStar_Pervasives_Native.Some
                                               uu____852)))))
                    | uu____868 ->
                        let uu____869 =
                          let uu____870 = FStar_Ident.string_of_lid nm  in
                          let uu____871 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____870 uu____871
                           in
                        failwith uu____869
  
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
                        | (a,uu____1023)::(b,uu____1025)::(c,uu____1027)::
                            (d,uu____1029)::(e,uu____1031)::(embedded_state,uu____1033)::[]
                            ->
                            let uu____1100 =
                              FStar_Tactics_Embedding.unembed_proofstate
                                embedded_state
                               in
                            FStar_Util.bind_opt uu____1100
                              (fun ps  ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps  in
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1113  ->
                                      let uu____1114 =
                                        FStar_Ident.string_of_lid nm  in
                                      let uu____1115 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state
                                         in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1114 uu____1115);
                                 (let uu____1116 = unembed_a a  in
                                  FStar_Util.bind_opt uu____1116
                                    (fun a1  ->
                                       let uu____1124 = unembed_b b  in
                                       FStar_Util.bind_opt uu____1124
                                         (fun b1  ->
                                            let uu____1132 = unembed_c c  in
                                            FStar_Util.bind_opt uu____1132
                                              (fun c1  ->
                                                 let uu____1140 = unembed_d d
                                                    in
                                                 FStar_Util.bind_opt
                                                   uu____1140
                                                   (fun d1  ->
                                                      let uu____1148 =
                                                        unembed_e e  in
                                                      FStar_Util.bind_opt
                                                        uu____1148
                                                        (fun e1  ->
                                                           let res =
                                                             let uu____1160 =
                                                               t a1 b1 c1 d1
                                                                 e1
                                                                in
                                                             FStar_Tactics_Basic.run
                                                               uu____1160 ps1
                                                              in
                                                           let uu____1163 =
                                                             let uu____1164 =
                                                               FStar_TypeChecker_Normalize.psc_range
                                                                 psc
                                                                in
                                                             let uu____1165 =
                                                               FStar_Tactics_Embedding.embed_result
                                                                 embed_r t_r
                                                                in
                                                             uu____1165
                                                               uu____1164 res
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1163)))))))
                        | uu____1179 ->
                            let uu____1180 =
                              let uu____1181 = FStar_Ident.string_of_lid nm
                                 in
                              let uu____1182 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1181 uu____1182
                               in
                            failwith uu____1180
  
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
  fun uu____1234  ->
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
      | (ps,uu____1722)::[] ->
          let uu____1739 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1739
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1747 =
                 let uu____1748 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1749 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1748
                   uu____1749
                  in
               FStar_Pervasives_Native.Some uu____1747)
      | uu____1750 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____1754 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1754;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____1767)::[] ->
          let uu____1784 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1784
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1792 =
                 let uu____1793 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1794 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1793
                   uu____1794
                  in
               FStar_Pervasives_Native.Some uu____1792)
      | uu____1795 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____1799 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1799;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____1816)::[] ->
          let uu____1833 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1833
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1846 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____1863)::(r,uu____1865)::[] ->
          let uu____1892 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1892
            (fun ps1  ->
               let uu____1898 = FStar_Syntax_Embeddings.unembed_range r  in
               FStar_Util.bind_opt uu____1898
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____1906 =
                      let uu____1907 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Tactics_Embedding.embed_proofstate uu____1907 ps'
                       in
                    FStar_Pervasives_Native.Some uu____1906))
      | uu____1908 ->
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
      let uu___59_1922 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___59_1922.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___59_1922.FStar_Syntax_Syntax.vars)
      }  in
    let get1 t = FStar_Pervasives_Native.Some t  in
    let uu____1929 =
      let uu____1932 =
        mktac2 () () () "__fail"
          (fun a434  ->
             fun a435  ->
               (Obj.magic (fun uu____1934  -> FStar_Tactics_Basic.fail)) a434
                 a435) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit
         in
      let uu____1935 =
        let uu____1938 =
          mktac0 () "__trivial" (Obj.magic FStar_Tactics_Basic.trivial)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit
           in
        let uu____1939 =
          let uu____1942 =
            let uu____1943 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit
               in
            mktac2 () () () "__trytac"
              (fun a436  ->
                 fun a437  ->
                   (Obj.magic (fun uu____1949  -> FStar_Tactics_Basic.trytac))
                     a436 a437) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____1943)
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1956 =
            let uu____1959 =
              mktac0 () "__intro" (Obj.magic FStar_Tactics_Basic.intro)
                (Obj.magic FStar_Reflection_Basic.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder
               in
            let uu____1960 =
              let uu____1963 =
                let uu____1964 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                let uu____1971 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                mktac0 () "__intro_rec"
                  (Obj.magic FStar_Tactics_Basic.intro_rec)
                  (Obj.magic uu____1964) uu____1971
                 in
              let uu____1978 =
                let uu____1981 =
                  let uu____1982 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step
                     in
                  mktac1 () () "__norm"
                    (fun a438  -> (Obj.magic FStar_Tactics_Basic.norm) a438)
                    (Obj.magic uu____1982)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit
                   in
                let uu____1991 =
                  let uu____1994 =
                    let uu____1995 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step
                       in
                    mktac3 () () () () "__norm_term_env"
                      (fun a439  ->
                         fun a440  ->
                           fun a441  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a439 a440 a441)
                      (Obj.magic FStar_Reflection_Basic.unembed_env)
                      (Obj.magic uu____1995)
                      (Obj.magic FStar_Reflection_Basic.unembed_term)
                      (Obj.magic FStar_Reflection_Basic.embed_term)
                      FStar_Syntax_Syntax.t_term
                     in
                  let uu____2004 =
                    let uu____2007 =
                      let uu____2008 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step
                         in
                      mktac2 () () () "__norm_binder_type"
                        (fun a442  ->
                           fun a443  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a442 a443) (Obj.magic uu____2008)
                        (Obj.magic FStar_Reflection_Basic.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2017 =
                      let uu____2020 =
                        mktac2 () () () "__rename_to"
                          (fun a444  ->
                             fun a445  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a444
                                 a445)
                          (Obj.magic FStar_Reflection_Basic.unembed_binder)
                          (Obj.magic FStar_Syntax_Embeddings.unembed_string)
                          (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                          FStar_Syntax_Syntax.t_unit
                         in
                      let uu____2021 =
                        let uu____2024 =
                          mktac1 () () "__binder_retype"
                            (fun a446  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a446)
                            (Obj.magic FStar_Reflection_Basic.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit
                           in
                        let uu____2025 =
                          let uu____2028 =
                            mktac0 () "__revert"
                              (Obj.magic FStar_Tactics_Basic.revert)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit
                             in
                          let uu____2029 =
                            let uu____2032 =
                              mktac0 () "__clear_top"
                                (Obj.magic FStar_Tactics_Basic.clear_top)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit
                               in
                            let uu____2033 =
                              let uu____2036 =
                                mktac1 () () "__clear"
                                  (fun a447  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a447)
                                  (Obj.magic
                                     FStar_Reflection_Basic.unembed_binder)
                                  (Obj.magic
                                     FStar_Syntax_Embeddings.embed_unit)
                                  FStar_Syntax_Syntax.t_unit
                                 in
                              let uu____2037 =
                                let uu____2040 =
                                  mktac1 () () "__rewrite"
                                    (fun a448  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a448)
                                    (Obj.magic
                                       FStar_Reflection_Basic.unembed_binder)
                                    (Obj.magic
                                       FStar_Syntax_Embeddings.embed_unit)
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                let uu____2041 =
                                  let uu____2044 =
                                    mktac0 () "__smt"
                                      (Obj.magic FStar_Tactics_Basic.smt)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit
                                     in
                                  let uu____2045 =
                                    let uu____2048 =
                                      mktac0 () "__refine_intro"
                                        (Obj.magic
                                           FStar_Tactics_Basic.refine_intro)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit
                                       in
                                    let uu____2049 =
                                      let uu____2052 =
                                        mktac3 () () () () "__t_exact"
                                          (fun a449  ->
                                             fun a450  ->
                                               fun a451  ->
                                                 (Obj.magic
                                                    FStar_Tactics_Basic.t_exact)
                                                   a449 a450 a451)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Reflection_Basic.unembed_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.embed_unit)
                                          FStar_Syntax_Syntax.t_unit
                                         in
                                      let uu____2053 =
                                        let uu____2056 =
                                          mktac1 () () "__apply"
                                            (fun a452  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a452)
                                            (Obj.magic
                                               FStar_Reflection_Basic.unembed_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_unit)
                                            FStar_Syntax_Syntax.t_unit
                                           in
                                        let uu____2057 =
                                          let uu____2060 =
                                            mktac1 () () "__apply_raw"
                                              (fun a453  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a453)
                                              (Obj.magic
                                                 FStar_Reflection_Basic.unembed_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.embed_unit)
                                              FStar_Syntax_Syntax.t_unit
                                             in
                                          let uu____2061 =
                                            let uu____2064 =
                                              mktac1 () () "__apply_lemma"
                                                (fun a454  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a454)
                                                (Obj.magic
                                                   FStar_Reflection_Basic.unembed_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.embed_unit)
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            let uu____2065 =
                                              let uu____2068 =
                                                let uu____2069 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a455  ->
                                                     fun a456  ->
                                                       fun a457  ->
                                                         fun a458  ->
                                                           fun a459  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2078
                                                                    ->
                                                                   fun
                                                                    uu____2079
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a455 a456 a457
                                                               a458 a459)
                                                  (Obj.magic get1)
                                                  (Obj.magic get1)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.unembed_int)
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic uu____2069)
                                                  FStar_Syntax_Syntax.t_unit
                                                 in
                                              let uu____2086 =
                                                let uu____2089 =
                                                  mktac1 () ()
                                                    "__set_options"
                                                    (fun a460  ->
                                                       (Obj.magic
                                                          FStar_Tactics_Basic.set_options)
                                                         a460)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.unembed_string)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.embed_unit)
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                let uu____2090 =
                                                  let uu____2093 =
                                                    mktac2 () () () "__seq"
                                                      (fun a461  ->
                                                         fun a462  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.seq)
                                                             a461 a462)
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
                                                  let uu____2094 =
                                                    let uu____2097 =
                                                      mktac1 () () "__tc"
                                                        (fun a463  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a463)
                                                        (Obj.magic
                                                           FStar_Reflection_Basic.unembed_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Basic.embed_term)
                                                        FStar_Syntax_Syntax.t_term
                                                       in
                                                    let uu____2098 =
                                                      let uu____2101 =
                                                        mktac1 () ()
                                                          "__unshelve"
                                                          (fun a464  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a464)
                                                          (Obj.magic
                                                             FStar_Reflection_Basic.unembed_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.embed_unit)
                                                          FStar_Syntax_Syntax.t_unit
                                                         in
                                                      let uu____2102 =
                                                        let uu____2105 =
                                                          mktac2 () () ()
                                                            "__unquote"
                                                            (fun a465  ->
                                                               fun a466  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a465 a466)
                                                            (Obj.magic get1)
                                                            (Obj.magic
                                                               FStar_Reflection_Basic.unembed_term)
                                                            (Obj.magic put1)
                                                            FStar_Syntax_Syntax.t_unit
                                                           in
                                                        let uu____2106 =
                                                          let uu____2109 =
                                                            mktac1 () ()
                                                              "__prune"
                                                              (fun a467  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a467)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.unembed_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.embed_unit)
                                                              FStar_Syntax_Syntax.t_unit
                                                             in
                                                          let uu____2110 =
                                                            let uu____2113 =
                                                              mktac1 () ()
                                                                "__addns"
                                                                (fun a468  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a468)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.embed_unit)
                                                                FStar_Syntax_Syntax.t_unit
                                                               in
                                                            let uu____2114 =
                                                              let uu____2117
                                                                =
                                                                mktac1 () ()
                                                                  "__print"
                                                                  (fun a469 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun x 
                                                                    ->
                                                                    FStar_Tactics_Basic.tacprint
                                                                    x;
                                                                    FStar_Tactics_Basic.ret
                                                                    ())) a469)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                  FStar_Syntax_Syntax.t_unit
                                                                 in
                                                              let uu____2122
                                                                =
                                                                let uu____2125
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "__dump"
                                                                    (
                                                                    fun a470 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a470)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                   in
                                                                let uu____2126
                                                                  =
                                                                  let uu____2129
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__dump1"
                                                                    (fun a471
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a471)
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
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a472
                                                                     ->
                                                                    fun a473 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a472 a473)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_direction)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2134
                                                                    =
                                                                    let uu____2137
                                                                    =
                                                                    mktac0 ()
                                                                    "__trefl"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2138
                                                                    =
                                                                    let uu____2141
                                                                    =
                                                                    mktac0 ()
                                                                    "__later"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2142
                                                                    =
                                                                    let uu____2145
                                                                    =
                                                                    mktac0 ()
                                                                    "__dup"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2146
                                                                    =
                                                                    let uu____2149
                                                                    =
                                                                    mktac0 ()
                                                                    "__flip"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2150
                                                                    =
                                                                    let uu____2153
                                                                    =
                                                                    mktac0 ()
                                                                    "__qed"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
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
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2165
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "__cases"
                                                                    (fun a474
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a474)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    (Obj.magic
                                                                    uu____2158)
                                                                    uu____2165
                                                                     in
                                                                    let uu____2172
                                                                    =
                                                                    let uu____2175
                                                                    =
                                                                    mktac0 ()
                                                                    "__top_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2176
                                                                    =
                                                                    let uu____2179
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2180
                                                                    =
                                                                    let uu____2183
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_goal"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2184
                                                                    =
                                                                    let uu____2187
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_witness"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2188
                                                                    =
                                                                    let uu____2191
                                                                    =
                                                                    mktac0 ()
                                                                    "__is_guard"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2192
                                                                    =
                                                                    let uu____2195
                                                                    =
                                                                    let uu____2196
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__uvar_env"
                                                                    (fun a475
                                                                     ->
                                                                    fun a476 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a475 a476)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_env)
                                                                    (Obj.magic
                                                                    uu____2196)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2205
                                                                    =
                                                                    let uu____2208
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__unify"
                                                                    (fun a477
                                                                     ->
                                                                    fun a478 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a477 a478)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2209
                                                                    =
                                                                    let uu____2212
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "__launch_process"
                                                                    (fun a479
                                                                     ->
                                                                    fun a480 
                                                                    ->
                                                                    fun a481 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a479 a480
                                                                    a481)
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
                                                                    [uu____2212;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step]
                                                                     in
                                                                    uu____2208
                                                                    ::
                                                                    uu____2209
                                                                     in
                                                                    uu____2195
                                                                    ::
                                                                    uu____2205
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
                                                                    uu____2175
                                                                    ::
                                                                    uu____2176
                                                                     in
                                                                    uu____2157
                                                                    ::
                                                                    uu____2172
                                                                     in
                                                                    uu____2153
                                                                    ::
                                                                    uu____2154
                                                                     in
                                                                    uu____2149
                                                                    ::
                                                                    uu____2150
                                                                     in
                                                                    uu____2145
                                                                    ::
                                                                    uu____2146
                                                                     in
                                                                    uu____2141
                                                                    ::
                                                                    uu____2142
                                                                     in
                                                                    uu____2137
                                                                    ::
                                                                    uu____2138
                                                                     in
                                                                    uu____2133
                                                                    ::
                                                                    uu____2134
                                                                     in
                                                                  uu____2129
                                                                    ::
                                                                    uu____2130
                                                                   in
                                                                uu____2125 ::
                                                                  uu____2126
                                                                 in
                                                              uu____2117 ::
                                                                uu____2122
                                                               in
                                                            uu____2113 ::
                                                              uu____2114
                                                             in
                                                          uu____2109 ::
                                                            uu____2110
                                                           in
                                                        uu____2105 ::
                                                          uu____2106
                                                         in
                                                      uu____2101 ::
                                                        uu____2102
                                                       in
                                                    uu____2097 :: uu____2098
                                                     in
                                                  uu____2093 :: uu____2094
                                                   in
                                                uu____2089 :: uu____2090  in
                                              uu____2068 :: uu____2086  in
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
                        uu____2024 :: uu____2025  in
                      uu____2020 :: uu____2021  in
                    uu____2007 :: uu____2017  in
                  uu____1994 :: uu____2004  in
                uu____1981 :: uu____1991  in
              uu____1963 :: uu____1978  in
            uu____1959 :: uu____1960  in
          uu____1942 :: uu____1956  in
        uu____1938 :: uu____1939  in
      uu____1932 :: uu____1935  in
    FStar_List.append uu____1929
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)

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
             let uu____2235 =
               let uu____2236 =
                 let uu____2237 =
                   let uu____2238 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____2238  in
                 [uu____2237]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2236  in
             uu____2235 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____2245 = FStar_ST.op_Bang tacdbg  in
            if uu____2245
            then
              let uu____2265 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2265
            else ());
           (let result =
              let uu____2268 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2268 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____2272 = FStar_ST.op_Bang tacdbg  in
             if uu____2272
             then
               let uu____2292 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2292
             else ());
            (let res =
               FStar_Tactics_Embedding.unembed_result result unembed_b  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2337 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2337
                   (fun uu____2341  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2364 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2364
                   (fun uu____2368  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2381 =
                   let uu____2386 =
                     let uu____2387 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2387
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2386)  in
                 FStar_Errors.raise_error uu____2381
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2396 = unembed_tactic_0 unembed_b embedded_tac_b  in
      FStar_All.pipe_left (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
        uu____2396

let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2452  ->
             match uu____2452 with
             | (r,uu____2472,uv,uu____2474,ty,rng) ->
                 let uu____2477 =
                   let uu____2478 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____2479 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2478 uu____2479 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____2477, rng)) is
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
        (let uu____2528 = FStar_ST.op_Bang tacdbg  in
         if uu____2528
         then
           let uu____2548 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2548
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         FStar_Errors.stop_if_err ();
         (let tau =
            unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic1  in
          let uu____2555 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____2555 with
          | (env1,uu____2569) ->
              let env2 =
                let uu___60_2575 = env1  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___60_2575.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___60_2575.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___60_2575.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___60_2575.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___60_2575.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___60_2575.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___60_2575.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___60_2575.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___60_2575.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp = false;
                  FStar_TypeChecker_Env.effects =
                    (uu___60_2575.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___60_2575.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___60_2575.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___60_2575.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___60_2575.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___60_2575.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___60_2575.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___60_2575.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___60_2575.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___60_2575.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___60_2575.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___60_2575.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___60_2575.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___60_2575.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___60_2575.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___60_2575.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___60_2575.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___60_2575.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___60_2575.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___60_2575.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___60_2575.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___60_2575.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___60_2575.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___60_2575.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___60_2575.FStar_TypeChecker_Env.dep_graph)
                }  in
              let uu____2576 =
                FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ  in
              (match uu____2576 with
               | (ps,w) ->
                   ((let uu____2590 = FStar_ST.op_Bang tacdbg  in
                     if uu____2590
                     then
                       let uu____2610 = FStar_Syntax_Print.term_to_string typ
                          in
                       FStar_Util.print1 "Running tactic with goal = %s\n"
                         uu____2610
                     else ());
                    (let uu____2612 = FStar_Tactics_Basic.run tau ps  in
                     match uu____2612 with
                     | FStar_Tactics_Result.Success (uu____2621,ps1) ->
                         ((let uu____2624 = FStar_ST.op_Bang tacdbg  in
                           if uu____2624
                           then
                             let uu____2644 =
                               FStar_Syntax_Print.term_to_string w  in
                             FStar_Util.print1
                               "Tactic generated proofterm %s\n" uu____2644
                           else ());
                          FStar_List.iter
                            (fun g  ->
                               let uu____2651 =
                                 FStar_Tactics_Basic.is_irrelevant g  in
                               if uu____2651
                               then
                                 let uu____2652 =
                                   FStar_TypeChecker_Rel.teq_nosmt
                                     g.FStar_Tactics_Types.context
                                     g.FStar_Tactics_Types.witness
                                     FStar_Syntax_Util.exp_unit
                                    in
                                 (if uu____2652
                                  then ()
                                  else
                                    (let uu____2654 =
                                       let uu____2655 =
                                         FStar_Syntax_Print.term_to_string
                                           g.FStar_Tactics_Types.witness
                                          in
                                       FStar_Util.format1
                                         "Irrelevant tactic witness does not unify with (): %s"
                                         uu____2655
                                        in
                                     failwith uu____2654))
                               else ())
                            (FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals);
                          (let g =
                             let uu___61_2658 =
                               FStar_TypeChecker_Rel.trivial_guard  in
                             {
                               FStar_TypeChecker_Env.guard_f =
                                 (uu___61_2658.FStar_TypeChecker_Env.guard_f);
                               FStar_TypeChecker_Env.deferred =
                                 (uu___61_2658.FStar_TypeChecker_Env.deferred);
                               FStar_TypeChecker_Env.univ_ineqs =
                                 (uu___61_2658.FStar_TypeChecker_Env.univ_ineqs);
                               FStar_TypeChecker_Env.implicits =
                                 (ps1.FStar_Tactics_Types.all_implicits)
                             }  in
                           let g1 =
                             let uu____2660 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____2660
                               FStar_TypeChecker_Rel.resolve_implicits_tac
                              in
                           report_implicits ps1
                             g1.FStar_TypeChecker_Env.implicits;
                           ((FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals), w)))
                     | FStar_Tactics_Result.Failed (s,ps1) ->
                         ((let uu____2667 =
                             let uu____2668 =
                               FStar_TypeChecker_Normalize.psc_subst
                                 ps1.FStar_Tactics_Types.psc
                                in
                             FStar_Tactics_Types.subst_proof_state uu____2668
                               ps1
                              in
                           FStar_Tactics_Basic.dump_proofstate uu____2667
                             "at the time of failure");
                          (let uu____2669 =
                             let uu____2674 =
                               FStar_Util.format1 "user tactic failed: %s" s
                                in
                             (FStar_Errors.Fatal_ArgumentLengthMismatch,
                               uu____2674)
                              in
                           FStar_Errors.raise_error uu____2669
                             typ.FStar_Syntax_Syntax.pos)))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2684 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2688 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2692 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2741 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2777 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2827 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____2865 . 'Auu____2865 -> 'Auu____2865 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____2884 = FStar_Syntax_Util.head_and_args t  in
        match uu____2884 with
        | (hd1,args) ->
            let uu____2921 =
              let uu____2934 =
                let uu____2935 = FStar_Syntax_Util.un_uinst hd1  in
                uu____2935.FStar_Syntax_Syntax.n  in
              (uu____2934, args)  in
            (match uu____2921 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2948))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3011 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3011 with
                       | (gs,uu____3019) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3026 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3026 with
                       | (gs,uu____3034) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3085 =
                        let uu____3092 =
                          let uu____3095 =
                            let uu____3096 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3096
                             in
                          [uu____3095]  in
                        (FStar_Syntax_Util.t_true, uu____3092)  in
                      Simplified uu____3085
                  | Both  ->
                      let uu____3107 =
                        let uu____3120 =
                          let uu____3123 =
                            let uu____3124 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3124
                             in
                          [uu____3123]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3120)  in
                      Dual uu____3107
                  | Neg  -> Simplified (assertion, []))
             | uu____3145 -> Unchanged t)
  
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
    fun uu___58_3225  ->
      match uu___58_3225 with
      | Unchanged t -> let uu____3231 = f t  in Unchanged uu____3231
      | Simplified (t,gs) ->
          let uu____3238 = let uu____3245 = f t  in (uu____3245, gs)  in
          Simplified uu____3238
      | Dual (tn,tp,gs) ->
          let uu____3255 =
            let uu____3264 = f tn  in
            let uu____3265 = f tp  in (uu____3264, uu____3265, gs)  in
          Dual uu____3255
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3319 = f t1 t2  in Unchanged uu____3319
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3331 = let uu____3338 = f t1 t2  in (uu____3338, gs)
               in
            Simplified uu____3331
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3352 = let uu____3359 = f t1 t2  in (uu____3359, gs)
               in
            Simplified uu____3352
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3378 =
              let uu____3385 = f t1 t2  in
              (uu____3385, (FStar_List.append gs1 gs2))  in
            Simplified uu____3378
        | uu____3388 ->
            let uu____3397 = explode x  in
            (match uu____3397 with
             | (n1,p1,gs1) ->
                 let uu____3415 = explode y  in
                 (match uu____3415 with
                  | (n2,p2,gs2) ->
                      let uu____3433 =
                        let uu____3442 = f n1 n2  in
                        let uu____3443 = f p1 p2  in
                        (uu____3442, uu____3443, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3433))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3508 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3508
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3551  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3585 =
              let uu____3586 = FStar_Syntax_Subst.compress t  in
              uu____3586.FStar_Syntax_Syntax.n  in
            match uu____3585 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3598 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3598 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3622 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3622 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3640;
                   FStar_Syntax_Syntax.vars = uu____3641;_},(p,uu____3643)::
                 (q,uu____3645)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3685 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3685
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3688 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3688 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3694 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3694.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3698;
                   FStar_Syntax_Syntax.vars = uu____3699;_},(p,uu____3701)::
                 (q,uu____3703)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3743 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3743
                   in
                let xq =
                  let uu____3745 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3745
                   in
                let r1 =
                  let uu____3747 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3747 p  in
                let r2 =
                  let uu____3749 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3749 q  in
                (match (r1, r2) with
                 | (Unchanged uu____3752,Unchanged uu____3753) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3763 = FStar_Syntax_Util.mk_iff l r  in
                            uu____3763.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3766 ->
                     let uu____3771 = explode r1  in
                     (match uu____3771 with
                      | (pn,pp,gs1) ->
                          let uu____3789 = explode r2  in
                          (match uu____3789 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3810 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____3811 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____3810
                                   uu____3811
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____3863  ->
                       fun r  ->
                         match uu____3863 with
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
                let uu____3981 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____3981 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4015  ->
                            match uu____4015 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4029 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___62_4053 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___62_4053.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___62_4053.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4029 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4073 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4073.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4119 = traverse f pol e t1  in
                let uu____4124 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4124 uu____4119
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___63_4162 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___63_4162.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___63_4162.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4169 =
                f pol e
                  (let uu___64_4173 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___64_4173.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___64_4173.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4169
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___65_4183 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___65_4183.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___65_4183.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4184 = explode rp  in
              (match uu____4184 with
               | (uu____4193,p',gs') ->
                   Dual
                     ((let uu___66_4207 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___66_4207.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___66_4207.FStar_Syntax_Syntax.vars)
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
      (let uu____4242 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4242);
      (let uu____4263 = FStar_ST.op_Bang tacdbg  in
       if uu____4263
       then
         let uu____4283 =
           let uu____4284 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4284
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4285 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4283
           uu____4285
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4314 =
         let uu____4321 = traverse by_tactic_interp Pos env goal  in
         match uu____4321 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4339 -> failwith "no"  in
       match uu____4314 with
       | (t',gs) ->
           ((let uu____4361 = FStar_ST.op_Bang tacdbg  in
             if uu____4361
             then
               let uu____4381 =
                 let uu____4382 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4382
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4383 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4381 uu____4383
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4430  ->
                    fun g  ->
                      match uu____4430 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4475 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____4475 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4478 =
                                  let uu____4479 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty
                                     in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4479
                                   in
                                failwith uu____4478
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4482 = FStar_ST.op_Bang tacdbg  in
                            if uu____4482
                            then
                              let uu____4502 = FStar_Util.string_of_int n1
                                 in
                              let uu____4503 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4502 uu____4503
                            else ());
                           (let gt' =
                              let uu____4506 =
                                let uu____4507 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4507
                                 in
                              FStar_TypeChecker_Util.label uu____4506
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____4522 = s1  in
             match uu____4522 with
             | (uu____4543,gs1) ->
                 let uu____4561 =
                   let uu____4568 = FStar_Options.peek ()  in
                   (env, t', uu____4568)  in
                 uu____4561 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4579 =
        let uu____4580 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4580  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4579 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4581 =
      let uu____4582 =
        let uu____4583 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4584 =
          let uu____4587 = FStar_Syntax_Syntax.as_arg a  in [uu____4587]  in
        uu____4583 :: uu____4584  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4582  in
    uu____4581 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4600 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____4600);
        (let uu____4620 =
           let uu____4627 = reify_tactic tau  in
           run_tactic_on_typ uu____4627 env typ  in
         match uu____4620 with
         | (gs,w) ->
             let uu____4634 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4638 =
                      let uu____4639 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____4639  in
                    Prims.op_Negation uu____4638) gs
                in
             if uu____4634
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                   "synthesis left open goals") typ.FStar_Syntax_Syntax.pos
             else w)
  