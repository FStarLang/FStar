open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let mk_tactic_interpretation_0 :
  'r .
    Prims.bool ->
      'r FStar_Tactics_Basic.tac ->
        'r FStar_Syntax_Embeddings.embedder ->
          FStar_Syntax_Syntax.typ ->
            FStar_Ident.lid ->
              FStar_TypeChecker_Normalize.psc ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun embed_r  ->
        fun t_r  ->
          fun nm  ->
            fun psc  ->
              fun args  ->
                match args with
                | (embedded_state,uu____68)::[] ->
                    let uu____85 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state
                       in
                    FStar_Util.bind_opt uu____85
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____98  ->
                              let uu____99 = FStar_Ident.string_of_lid nm  in
                              let uu____100 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.print2 "Reached %s, args are: %s\n"
                                uu____99 uu____100);
                         (let res =
                            let uu____102 =
                              FStar_TypeChecker_Normalize.psc_range psc  in
                            let uu____103 = FStar_Tactics_Basic.run t ps1  in
                            let uu____106 =
                              FStar_Tactics_Embedding.embed_result embed_r
                                t_r
                               in
                            uu____106 uu____102 uu____103  in
                          FStar_Pervasives_Native.Some res))
                | uu____120 ->
                    failwith "Unexpected application of tactic primitive"
  
let mk_tactic_interpretation_1 :
  'a 'r .
    Prims.bool ->
      ('a -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'r FStar_Syntax_Embeddings.embedder ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_TypeChecker_Normalize.psc ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun embed_r  ->
          fun t_r  ->
            fun nm  ->
              fun psc  ->
                fun args  ->
                  match args with
                  | (a,uu____197)::(embedded_state,uu____199)::[] ->
                      let uu____226 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state
                         in
                      FStar_Util.bind_opt uu____226
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____239  ->
                                let uu____240 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____241 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____240
                                  uu____241);
                           (let uu____242 = unembed_a a  in
                            FStar_Util.bind_opt uu____242
                              (fun a1  ->
                                 let res =
                                   let uu____254 = t a1  in
                                   FStar_Tactics_Basic.run uu____254 ps1  in
                                 let uu____257 =
                                   let uu____258 =
                                     FStar_TypeChecker_Normalize.psc_range
                                       psc
                                      in
                                   let uu____259 =
                                     FStar_Tactics_Embedding.embed_result
                                       embed_r t_r
                                      in
                                   uu____259 uu____258 res  in
                                 FStar_Pervasives_Native.Some uu____257)))
                  | uu____273 ->
                      let uu____274 =
                        let uu____275 = FStar_Ident.string_of_lid nm  in
                        let uu____276 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____275 uu____276
                         in
                      failwith uu____274
  
let mk_tactic_interpretation_1_env :
  'a 'r .
    Prims.bool ->
      (FStar_TypeChecker_Normalize.psc -> 'a -> 'r FStar_Tactics_Basic.tac)
        ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'r FStar_Syntax_Embeddings.embedder ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_TypeChecker_Normalize.psc ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun embed_r  ->
          fun t_r  ->
            fun nm  ->
              fun psc  ->
                fun args  ->
                  match args with
                  | (a,uu____358)::(embedded_state,uu____360)::[] ->
                      let uu____387 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state
                         in
                      FStar_Util.bind_opt uu____387
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____400  ->
                                let uu____401 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____402 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____401
                                  uu____402);
                           (let uu____403 = unembed_a a  in
                            FStar_Util.bind_opt uu____403
                              (fun a1  ->
                                 let res =
                                   let uu____415 = t psc a1  in
                                   FStar_Tactics_Basic.run uu____415 ps1  in
                                 let uu____418 =
                                   let uu____419 =
                                     FStar_TypeChecker_Normalize.psc_range
                                       psc
                                      in
                                   let uu____420 =
                                     FStar_Tactics_Embedding.embed_result
                                       embed_r t_r
                                      in
                                   uu____420 uu____419 res  in
                                 FStar_Pervasives_Native.Some uu____418)))
                  | uu____434 ->
                      let uu____435 =
                        let uu____436 = FStar_Ident.string_of_lid nm  in
                        let uu____437 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____436 uu____437
                         in
                      failwith uu____435
  
let mk_tactic_interpretation_2 :
  'a 'b 'r .
    Prims.bool ->
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
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun unembed_b  ->
          fun embed_r  ->
            fun t_r  ->
              fun nm  ->
                fun psc  ->
                  fun args  ->
                    match args with
                    | (a,uu____534)::(b,uu____536)::(embedded_state,uu____538)::[]
                        ->
                        let uu____575 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state
                           in
                        FStar_Util.bind_opt uu____575
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____588  ->
                                  let uu____589 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____590 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state
                                     in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____589
                                    uu____590);
                             (let uu____591 = unembed_a a  in
                              FStar_Util.bind_opt uu____591
                                (fun a1  ->
                                   let uu____599 = unembed_b b  in
                                   FStar_Util.bind_opt uu____599
                                     (fun b1  ->
                                        let res =
                                          let uu____611 = t a1 b1  in
                                          FStar_Tactics_Basic.run uu____611
                                            ps1
                                           in
                                        let uu____614 =
                                          let uu____615 =
                                            FStar_TypeChecker_Normalize.psc_range
                                              psc
                                             in
                                          let uu____616 =
                                            FStar_Tactics_Embedding.embed_result
                                              embed_r t_r
                                             in
                                          uu____616 uu____615 res  in
                                        FStar_Pervasives_Native.Some
                                          uu____614))))
                    | uu____630 ->
                        let uu____631 =
                          let uu____632 = FStar_Ident.string_of_lid nm  in
                          let uu____633 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____632 uu____633
                           in
                        failwith uu____631
  
let mk_tactic_interpretation_3 :
  'a 'b 'c 'r .
    Prims.bool ->
      ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'b FStar_Syntax_Embeddings.unembedder ->
            'c FStar_Syntax_Embeddings.unembedder ->
              'r FStar_Syntax_Embeddings.embedder ->
                FStar_Syntax_Syntax.typ ->
                  FStar_Ident.lid ->
                    FStar_TypeChecker_Normalize.psc ->
                      FStar_Syntax_Syntax.args ->
                        FStar_Syntax_Syntax.term
                          FStar_Pervasives_Native.option
  =
  fun reflect  ->
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
                      | (a,uu____750)::(b,uu____752)::(c,uu____754)::
                          (embedded_state,uu____756)::[] ->
                          let uu____803 =
                            FStar_Tactics_Embedding.unembed_proofstate
                              embedded_state
                             in
                          FStar_Util.bind_opt uu____803
                            (fun ps  ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               FStar_Tactics_Basic.log ps1
                                 (fun uu____816  ->
                                    let uu____817 =
                                      FStar_Ident.string_of_lid nm  in
                                    let uu____818 =
                                      FStar_Syntax_Print.term_to_string
                                        embedded_state
                                       in
                                    FStar_Util.print2
                                      "Reached %s, goals are: %s\n" uu____817
                                      uu____818);
                               (let uu____819 = unembed_a a  in
                                FStar_Util.bind_opt uu____819
                                  (fun a1  ->
                                     let uu____827 = unembed_b b  in
                                     FStar_Util.bind_opt uu____827
                                       (fun b1  ->
                                          let uu____835 = unembed_c c  in
                                          FStar_Util.bind_opt uu____835
                                            (fun c1  ->
                                               let res =
                                                 let uu____847 = t a1 b1 c1
                                                    in
                                                 FStar_Tactics_Basic.run
                                                   uu____847 ps1
                                                  in
                                               let uu____850 =
                                                 let uu____851 =
                                                   FStar_TypeChecker_Normalize.psc_range
                                                     psc
                                                    in
                                                 let uu____852 =
                                                   FStar_Tactics_Embedding.embed_result
                                                     embed_r t_r
                                                    in
                                                 uu____852 uu____851 res  in
                                               FStar_Pervasives_Native.Some
                                                 uu____850)))))
                      | uu____866 ->
                          let uu____867 =
                            let uu____868 = FStar_Ident.string_of_lid nm  in
                            let uu____869 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____868 uu____869
                             in
                          failwith uu____867
  
let mk_tactic_interpretation_5 :
  'a 'b 'c 'd 'e 'r .
    Prims.bool ->
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
  fun reflect  ->
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
                          | (a,uu____1026)::(b,uu____1028)::(c,uu____1030)::
                              (d,uu____1032)::(e,uu____1034)::(embedded_state,uu____1036)::[]
                              ->
                              let uu____1103 =
                                FStar_Tactics_Embedding.unembed_proofstate
                                  embedded_state
                                 in
                              FStar_Util.bind_opt uu____1103
                                (fun ps  ->
                                   let ps1 =
                                     FStar_Tactics_Types.set_ps_psc psc ps
                                      in
                                   FStar_Tactics_Basic.log ps1
                                     (fun uu____1116  ->
                                        let uu____1117 =
                                          FStar_Ident.string_of_lid nm  in
                                        let uu____1118 =
                                          FStar_Syntax_Print.term_to_string
                                            embedded_state
                                           in
                                        FStar_Util.print2
                                          "Reached %s, goals are: %s\n"
                                          uu____1117 uu____1118);
                                   (let uu____1119 = unembed_a a  in
                                    FStar_Util.bind_opt uu____1119
                                      (fun a1  ->
                                         let uu____1127 = unembed_b b  in
                                         FStar_Util.bind_opt uu____1127
                                           (fun b1  ->
                                              let uu____1135 = unembed_c c
                                                 in
                                              FStar_Util.bind_opt uu____1135
                                                (fun c1  ->
                                                   let uu____1143 =
                                                     unembed_d d  in
                                                   FStar_Util.bind_opt
                                                     uu____1143
                                                     (fun d1  ->
                                                        let uu____1151 =
                                                          unembed_e e  in
                                                        FStar_Util.bind_opt
                                                          uu____1151
                                                          (fun e1  ->
                                                             let res =
                                                               let uu____1163
                                                                 =
                                                                 t a1 b1 c1
                                                                   d1 e1
                                                                  in
                                                               FStar_Tactics_Basic.run
                                                                 uu____1163
                                                                 ps1
                                                                in
                                                             let uu____1166 =
                                                               let uu____1167
                                                                 =
                                                                 FStar_TypeChecker_Normalize.psc_range
                                                                   psc
                                                                  in
                                                               let uu____1168
                                                                 =
                                                                 FStar_Tactics_Embedding.embed_result
                                                                   embed_r
                                                                   t_r
                                                                  in
                                                               uu____1168
                                                                 uu____1167
                                                                 res
                                                                in
                                                             FStar_Pervasives_Native.Some
                                                               uu____1166)))))))
                          | uu____1182 ->
                              let uu____1183 =
                                let uu____1184 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____1185 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format2
                                  "Unexpected application of tactic primitive %s %s"
                                  uu____1184 uu____1185
                                 in
                              failwith uu____1183
  
let (step_from_native_step :
  FStar_Tactics_Native.native_primitive_step ->
    FStar_TypeChecker_Normalize.primitive_step)
  =
  fun s  ->
    {
      FStar_TypeChecker_Normalize.name = (s.FStar_Tactics_Native.name);
      FStar_TypeChecker_Normalize.arity = (s.FStar_Tactics_Native.arity);
      FStar_TypeChecker_Normalize.auto_reflect =
        (FStar_Pervasives_Native.Some
           (s.FStar_Tactics_Native.arity - (Prims.parse_int "1")));
      FStar_TypeChecker_Normalize.strong_reduction_ok =
        (s.FStar_Tactics_Native.strong_reduction_ok);
      FStar_TypeChecker_Normalize.requires_binder_substitution = false;
      FStar_TypeChecker_Normalize.interpretation =
        (fun psc  -> fun args  -> s.FStar_Tactics_Native.tactic psc args)
    }
  
let rec (primitive_steps :
  Prims.unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  fun uu____1271  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm]
         in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation =
          (fun psc  -> fun args  -> interpretation nm1 psc args)
      }  in
    let native_tactics = FStar_Tactics_Native.list_all ()  in
    let native_tactics_steps =
      FStar_List.map step_from_native_step native_tactics  in
    let mktac0 r name f e_r tr =
      mk1 name (Prims.parse_int "1")
        (mk_tactic_interpretation_0 false f e_r tr)
       in
    let mktac1 a r name f u_a e_r tr =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 false f u_a e_r tr)
       in
    let mktac2 a b r name f u_a u_b e_r tr =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 false f u_a u_b e_r tr)
       in
    let mktac3 a b c r name f u_a u_b u_c e_r tr =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 false f u_a u_b u_c e_r tr)
       in
    let mktac5 a b c d e r name f u_a u_b u_c u_d u_e e_r tr =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 false f u_a u_b u_c u_d u_e e_r tr)
       in
    let decr_depth_interp psc args =
      match args with
      | (ps,uu____1759)::[] ->
          let uu____1776 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1776
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1784 =
                 let uu____1785 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1786 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1785
                   uu____1786
                  in
               FStar_Pervasives_Native.Some uu____1784)
      | uu____1787 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____1791 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1791;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____1804)::[] ->
          let uu____1821 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1821
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1829 =
                 let uu____1830 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1831 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1830
                   uu____1831
                  in
               FStar_Pervasives_Native.Some uu____1829)
      | uu____1832 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____1836 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1836;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____1853)::[] ->
          let uu____1870 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1870
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1883 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____1900)::(r,uu____1902)::[] ->
          let uu____1929 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1929
            (fun ps1  ->
               let uu____1935 = FStar_Syntax_Embeddings.unembed_range r  in
               FStar_Util.bind_opt uu____1935
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____1943 =
                      let uu____1944 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Tactics_Embedding.embed_proofstate uu____1944 ps'
                       in
                    FStar_Pervasives_Native.Some uu____1943))
      | uu____1945 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let set_proofstate_range_step =
      let nm =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
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
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      }  in
    let put1 rng t =
      let uu___58_1959 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___58_1959.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___58_1959.FStar_Syntax_Syntax.vars)
      }  in
    let get1 t = FStar_Pervasives_Native.Some t  in
    let uu____1966 =
      let uu____1969 =
        mktac2 () () () "__fail"
          (fun a436  ->
             fun a437  ->
               (Obj.magic (fun uu____1971  -> FStar_Tactics_Basic.fail)) a436
                 a437) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit
         in
      let uu____1972 =
        let uu____1975 =
          mktac0 () "__trivial" (Obj.magic FStar_Tactics_Basic.trivial)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit
           in
        let uu____1976 =
          let uu____1979 =
            let uu____1980 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit
               in
            mktac2 () () () "__trytac"
              (fun a438  ->
                 fun a439  ->
                   (Obj.magic (fun uu____1986  -> FStar_Tactics_Basic.trytac))
                     a438 a439) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____1980)
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1993 =
            let uu____1996 =
              mktac0 () "__intro" (Obj.magic FStar_Tactics_Basic.intro)
                (Obj.magic FStar_Reflection_Embeddings.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder
               in
            let uu____1997 =
              let uu____2000 =
                let uu____2001 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                let uu____2008 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                mktac0 () "__intro_rec"
                  (Obj.magic FStar_Tactics_Basic.intro_rec)
                  (Obj.magic uu____2001) uu____2008
                 in
              let uu____2015 =
                let uu____2018 =
                  let uu____2019 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step
                     in
                  mktac1 () () "__norm"
                    (fun a440  -> (Obj.magic FStar_Tactics_Basic.norm) a440)
                    (Obj.magic uu____2019)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit
                   in
                let uu____2028 =
                  let uu____2031 =
                    let uu____2032 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step
                       in
                    mktac3 () () () () "__norm_term_env"
                      (fun a441  ->
                         fun a442  ->
                           fun a443  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a441 a442 a443)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_env)
                      (Obj.magic uu____2032)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_term)
                      (Obj.magic FStar_Reflection_Embeddings.embed_term)
                      FStar_Syntax_Syntax.t_term
                     in
                  let uu____2041 =
                    let uu____2044 =
                      let uu____2045 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step
                         in
                      mktac2 () () () "__norm_binder_type"
                        (fun a444  ->
                           fun a445  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a444 a445) (Obj.magic uu____2045)
                        (Obj.magic FStar_Reflection_Embeddings.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2054 =
                      let uu____2057 =
                        mktac2 () () () "__rename_to"
                          (fun a446  ->
                             fun a447  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a446
                                 a447)
                          (Obj.magic
                             FStar_Reflection_Embeddings.unembed_binder)
                          (Obj.magic FStar_Syntax_Embeddings.unembed_string)
                          (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                          FStar_Syntax_Syntax.t_unit
                         in
                      let uu____2058 =
                        let uu____2061 =
                          mktac1 () () "__binder_retype"
                            (fun a448  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a448)
                            (Obj.magic
                               FStar_Reflection_Embeddings.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit
                           in
                        let uu____2062 =
                          let uu____2065 =
                            mktac0 () "__revert"
                              (Obj.magic FStar_Tactics_Basic.revert)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit
                             in
                          let uu____2066 =
                            let uu____2069 =
                              mktac0 () "__clear_top"
                                (Obj.magic FStar_Tactics_Basic.clear_top)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit
                               in
                            let uu____2070 =
                              let uu____2073 =
                                mktac1 () () "__clear"
                                  (fun a449  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a449)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.unembed_binder)
                                  (Obj.magic
                                     FStar_Syntax_Embeddings.embed_unit)
                                  FStar_Syntax_Syntax.t_unit
                                 in
                              let uu____2074 =
                                let uu____2077 =
                                  mktac1 () () "__rewrite"
                                    (fun a450  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a450)
                                    (Obj.magic
                                       FStar_Reflection_Embeddings.unembed_binder)
                                    (Obj.magic
                                       FStar_Syntax_Embeddings.embed_unit)
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                let uu____2078 =
                                  let uu____2081 =
                                    mktac0 () "__smt"
                                      (Obj.magic FStar_Tactics_Basic.smt)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit
                                     in
                                  let uu____2082 =
                                    let uu____2085 =
                                      mktac0 () "__refine_intro"
                                        (Obj.magic
                                           FStar_Tactics_Basic.refine_intro)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit
                                       in
                                    let uu____2086 =
                                      let uu____2089 =
                                        mktac2 () () () "__t_exact"
                                          (fun a451  ->
                                             fun a452  ->
                                               (Obj.magic
                                                  FStar_Tactics_Basic.t_exact)
                                                 a451 a452)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Reflection_Embeddings.unembed_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.embed_unit)
                                          FStar_Syntax_Syntax.t_unit
                                         in
                                      let uu____2090 =
                                        let uu____2093 =
                                          mktac1 () () "__apply"
                                            (fun a453  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a453)
                                            (Obj.magic
                                               FStar_Reflection_Embeddings.unembed_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_unit)
                                            FStar_Syntax_Syntax.t_unit
                                           in
                                        let uu____2094 =
                                          let uu____2097 =
                                            mktac1 () () "__apply_raw"
                                              (fun a454  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a454)
                                              (Obj.magic
                                                 FStar_Reflection_Embeddings.unembed_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.embed_unit)
                                              FStar_Syntax_Syntax.t_unit
                                             in
                                          let uu____2098 =
                                            let uu____2101 =
                                              mktac1 () () "__apply_lemma"
                                                (fun a455  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a455)
                                                (Obj.magic
                                                   FStar_Reflection_Embeddings.unembed_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.embed_unit)
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            let uu____2102 =
                                              let uu____2105 =
                                                let uu____2106 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a456  ->
                                                     fun a457  ->
                                                       fun a458  ->
                                                         fun a459  ->
                                                           fun a460  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2115
                                                                    ->
                                                                   fun
                                                                    uu____2116
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a456 a457 a458
                                                               a459 a460)
                                                  (Obj.magic get1)
                                                  (Obj.magic get1)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.unembed_int)
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic uu____2106)
                                                  FStar_Syntax_Syntax.t_unit
                                                 in
                                              let uu____2123 =
                                                let uu____2126 =
                                                  mktac1 () ()
                                                    "__set_options"
                                                    (fun a461  ->
                                                       (Obj.magic
                                                          FStar_Tactics_Basic.set_options)
                                                         a461)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.unembed_string)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.embed_unit)
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                let uu____2127 =
                                                  let uu____2130 =
                                                    mktac2 () () () "__seq"
                                                      (fun a462  ->
                                                         fun a463  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.seq)
                                                             a462 a463)
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
                                                  let uu____2131 =
                                                    let uu____2134 =
                                                      mktac1 () () "__tc"
                                                        (fun a464  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a464)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.unembed_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.embed_term)
                                                        FStar_Syntax_Syntax.t_term
                                                       in
                                                    let uu____2135 =
                                                      let uu____2138 =
                                                        mktac1 () ()
                                                          "__unshelve"
                                                          (fun a465  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a465)
                                                          (Obj.magic
                                                             FStar_Reflection_Embeddings.unembed_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.embed_unit)
                                                          FStar_Syntax_Syntax.t_unit
                                                         in
                                                      let uu____2139 =
                                                        let uu____2142 =
                                                          mktac2 () () ()
                                                            "__unquote"
                                                            (fun a466  ->
                                                               fun a467  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a466 a467)
                                                            (Obj.magic get1)
                                                            (Obj.magic
                                                               FStar_Reflection_Embeddings.unembed_term)
                                                            (Obj.magic put1)
                                                            FStar_Syntax_Syntax.t_unit
                                                           in
                                                        let uu____2143 =
                                                          let uu____2146 =
                                                            mktac1 () ()
                                                              "__prune"
                                                              (fun a468  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a468)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.unembed_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.embed_unit)
                                                              FStar_Syntax_Syntax.t_unit
                                                             in
                                                          let uu____2147 =
                                                            let uu____2150 =
                                                              mktac1 () ()
                                                                "__addns"
                                                                (fun a469  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a469)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.embed_unit)
                                                                FStar_Syntax_Syntax.t_unit
                                                               in
                                                            let uu____2151 =
                                                              let uu____2154
                                                                =
                                                                mktac1 () ()
                                                                  "__print"
                                                                  (fun a470 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun x 
                                                                    ->
                                                                    FStar_Tactics_Basic.tacprint
                                                                    x;
                                                                    FStar_Tactics_Basic.ret
                                                                    ())) a470)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                  FStar_Syntax_Syntax.t_unit
                                                                 in
                                                              let uu____2159
                                                                =
                                                                let uu____2162
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "__dump"
                                                                    (
                                                                    fun a471 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a471)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                   in
                                                                let uu____2163
                                                                  =
                                                                  let uu____2166
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__dump1"
                                                                    (fun a472
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a472)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                  let uu____2167
                                                                    =
                                                                    let uu____2170
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a473
                                                                     ->
                                                                    fun a474 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a473 a474)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_direction)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2171
                                                                    =
                                                                    let uu____2174
                                                                    =
                                                                    let uu____2175
                                                                    =
                                                                    let uu____2186
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_pair
                                                                    FStar_Syntax_Embeddings.unembed_bool
                                                                    FStar_Syntax_Embeddings.unembed_int
                                                                     in
                                                                    unembed_tactic_1
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    uu____2186
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__topdown_rewrite"
                                                                    (fun a475
                                                                     ->
                                                                    fun a476 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.topdown_rewrite)
                                                                    a475 a476)
                                                                    (Obj.magic
                                                                    uu____2175)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2205
                                                                    =
                                                                    let uu____2208
                                                                    =
                                                                    mktac0 ()
                                                                    "__trefl"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2209
                                                                    =
                                                                    let uu____2212
                                                                    =
                                                                    mktac0 ()
                                                                    "__later"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2213
                                                                    =
                                                                    let uu____2216
                                                                    =
                                                                    mktac0 ()
                                                                    "__dup"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2217
                                                                    =
                                                                    let uu____2220
                                                                    =
                                                                    mktac0 ()
                                                                    "__flip"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2221
                                                                    =
                                                                    let uu____2224
                                                                    =
                                                                    mktac0 ()
                                                                    "__qed"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2225
                                                                    =
                                                                    let uu____2228
                                                                    =
                                                                    let uu____2229
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2236
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "__cases"
                                                                    (fun a477
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a477)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    uu____2229)
                                                                    uu____2236
                                                                     in
                                                                    let uu____2243
                                                                    =
                                                                    let uu____2246
                                                                    =
                                                                    mktac0 ()
                                                                    "__top_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2247
                                                                    =
                                                                    let uu____2250
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2251
                                                                    =
                                                                    let uu____2254
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_goal"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2255
                                                                    =
                                                                    let uu____2258
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_witness"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2259
                                                                    =
                                                                    let uu____2262
                                                                    =
                                                                    mktac0 ()
                                                                    "__is_guard"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2263
                                                                    =
                                                                    let uu____2266
                                                                    =
                                                                    let uu____2267
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Embeddings.unembed_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__uvar_env"
                                                                    (fun a478
                                                                     ->
                                                                    fun a479 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a478 a479)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_env)
                                                                    (Obj.magic
                                                                    uu____2267)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2276
                                                                    =
                                                                    let uu____2279
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__unify"
                                                                    (fun a480
                                                                     ->
                                                                    fun a481 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a480 a481)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2280
                                                                    =
                                                                    let uu____2283
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "__launch_process"
                                                                    (fun a482
                                                                     ->
                                                                    fun a483 
                                                                    ->
                                                                    fun a484 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a482 a483
                                                                    a484)
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
                                                                    let uu____2284
                                                                    =
                                                                    let uu____2287
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__fresh_bv_named"
                                                                    (fun a485
                                                                     ->
                                                                    fun a486 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh_bv_named)
                                                                    a485 a486)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_bv)
                                                                    FStar_Syntax_Syntax.t_bv
                                                                     in
                                                                    let uu____2288
                                                                    =
                                                                    let uu____2291
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__change"
                                                                    (fun a487
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.change)
                                                                    a487)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2292
                                                                    =
                                                                    let uu____2295
                                                                    =
                                                                    mktac0 ()
                                                                    "__get_guard_policy"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.get_guard_policy)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.embed_guard_policy)
                                                                    FStar_Tactics_Embedding.t_guard_policy
                                                                     in
                                                                    let uu____2296
                                                                    =
                                                                    let uu____2299
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__set_guard_policy"
                                                                    (fun a488
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.set_guard_policy)
                                                                    a488)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_guard_policy)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    [uu____2299;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step]
                                                                     in
                                                                    uu____2295
                                                                    ::
                                                                    uu____2296
                                                                     in
                                                                    uu____2291
                                                                    ::
                                                                    uu____2292
                                                                     in
                                                                    uu____2287
                                                                    ::
                                                                    uu____2288
                                                                     in
                                                                    uu____2283
                                                                    ::
                                                                    uu____2284
                                                                     in
                                                                    uu____2279
                                                                    ::
                                                                    uu____2280
                                                                     in
                                                                    uu____2266
                                                                    ::
                                                                    uu____2276
                                                                     in
                                                                    uu____2262
                                                                    ::
                                                                    uu____2263
                                                                     in
                                                                    uu____2258
                                                                    ::
                                                                    uu____2259
                                                                     in
                                                                    uu____2254
                                                                    ::
                                                                    uu____2255
                                                                     in
                                                                    uu____2250
                                                                    ::
                                                                    uu____2251
                                                                     in
                                                                    uu____2246
                                                                    ::
                                                                    uu____2247
                                                                     in
                                                                    uu____2228
                                                                    ::
                                                                    uu____2243
                                                                     in
                                                                    uu____2224
                                                                    ::
                                                                    uu____2225
                                                                     in
                                                                    uu____2220
                                                                    ::
                                                                    uu____2221
                                                                     in
                                                                    uu____2216
                                                                    ::
                                                                    uu____2217
                                                                     in
                                                                    uu____2212
                                                                    ::
                                                                    uu____2213
                                                                     in
                                                                    uu____2208
                                                                    ::
                                                                    uu____2209
                                                                     in
                                                                    uu____2174
                                                                    ::
                                                                    uu____2205
                                                                     in
                                                                    uu____2170
                                                                    ::
                                                                    uu____2171
                                                                     in
                                                                  uu____2166
                                                                    ::
                                                                    uu____2167
                                                                   in
                                                                uu____2162 ::
                                                                  uu____2163
                                                                 in
                                                              uu____2154 ::
                                                                uu____2159
                                                               in
                                                            uu____2150 ::
                                                              uu____2151
                                                             in
                                                          uu____2146 ::
                                                            uu____2147
                                                           in
                                                        uu____2142 ::
                                                          uu____2143
                                                         in
                                                      uu____2138 ::
                                                        uu____2139
                                                       in
                                                    uu____2134 :: uu____2135
                                                     in
                                                  uu____2130 :: uu____2131
                                                   in
                                                uu____2126 :: uu____2127  in
                                              uu____2105 :: uu____2123  in
                                            uu____2101 :: uu____2102  in
                                          uu____2097 :: uu____2098  in
                                        uu____2093 :: uu____2094  in
                                      uu____2089 :: uu____2090  in
                                    uu____2085 :: uu____2086  in
                                  uu____2081 :: uu____2082  in
                                uu____2077 :: uu____2078  in
                              uu____2073 :: uu____2074  in
                            uu____2069 :: uu____2070  in
                          uu____2065 :: uu____2066  in
                        uu____2061 :: uu____2062  in
                      uu____2057 :: uu____2058  in
                    uu____2044 :: uu____2054  in
                  uu____2031 :: uu____2041  in
                uu____2018 :: uu____2028  in
              uu____2000 :: uu____2015  in
            uu____1996 :: uu____1997  in
          uu____1979 :: uu____1993  in
        uu____1975 :: uu____1976  in
      uu____1969 :: uu____1972  in
    FStar_List.append uu____1966
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
               let uu____2329 =
                 let uu____2330 =
                   let uu____2331 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____2331]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____2330  in
               uu____2329 FStar_Pervasives_Native.None rng  in
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
             let uu____2360 =
               let uu____2361 =
                 let uu____2362 =
                   let uu____2363 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____2363  in
                 [uu____2362]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2361  in
             uu____2360 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____2370 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____2370
            then
              let uu____2371 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2371
            else ());
           (let result =
              let uu____2374 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2374 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____2378 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____2378
             then
               let uu____2379 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2379
             else ());
            (let res =
               FStar_Tactics_Embedding.unembed_result result unembed_b  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2424 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2424
                   (fun uu____2428  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2451 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2451
                   (fun uu____2455  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2468 =
                   let uu____2473 =
                     let uu____2474 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2474
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2473)  in
                 FStar_Errors.raise_error uu____2468
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2483 = unembed_tactic_0 unembed_b embedded_tac_b  in
      FStar_All.pipe_left (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
        uu____2483

let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2539  ->
             match uu____2539 with
             | (r,uu____2559,uv,uu____2561,ty,rng) ->
                 let uu____2564 =
                   let uu____2565 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____2566 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2565 uu____2566 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____2564, rng)) is
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
        (let uu____2615 = FStar_ST.op_Bang tacdbg  in
         if uu____2615
         then
           let uu____2635 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2635
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         (let uu____2639 = FStar_ST.op_Bang tacdbg  in
          if uu____2639
          then
            let uu____2659 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____2659
          else ());
         (let uu____2661 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
          match uu____2661 with
          | (uu____2674,uu____2675,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic1
                   in
                let uu____2682 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                match uu____2682 with
                | (env1,uu____2696) ->
                    let env2 =
                      let uu___59_2702 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___59_2702.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___59_2702.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___59_2702.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___59_2702.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___59_2702.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___59_2702.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___59_2702.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___59_2702.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___59_2702.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___59_2702.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___59_2702.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___59_2702.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___59_2702.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___59_2702.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___59_2702.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___59_2702.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___59_2702.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___59_2702.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___59_2702.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___59_2702.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___59_2702.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___59_2702.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___59_2702.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___59_2702.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___59_2702.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___59_2702.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___59_2702.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___59_2702.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth =
                          (uu___59_2702.FStar_TypeChecker_Env.synth);
                        FStar_TypeChecker_Env.splice =
                          (uu___59_2702.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___59_2702.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___59_2702.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___59_2702.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___59_2702.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___59_2702.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let uu____2703 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ  in
                    (match uu____2703 with
                     | (ps,w) ->
                         ((let uu____2717 = FStar_ST.op_Bang tacdbg  in
                           if uu____2717
                           then
                             let uu____2737 =
                               FStar_Syntax_Print.term_to_string typ  in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____2737
                           else ());
                          (let uu____2739 =
                             FStar_Util.record_time
                               (fun uu____2749  ->
                                  FStar_Tactics_Basic.run tau ps)
                              in
                           match uu____2739 with
                           | (res,ms) ->
                               ((let uu____2763 = FStar_ST.op_Bang tacdbg  in
                                 if uu____2763
                                 then
                                   let uu____2783 =
                                     FStar_Syntax_Print.term_to_string
                                       tactic1
                                      in
                                   let uu____2784 =
                                     FStar_Util.string_of_int ms  in
                                   let uu____2785 =
                                     FStar_Syntax_Print.lid_to_string
                                       env2.FStar_TypeChecker_Env.curmodule
                                      in
                                   FStar_Util.print3
                                     "Tactic %s ran in %s ms (%s)\n"
                                     uu____2783 uu____2784 uu____2785
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____2793,ps1) ->
                                     ((let uu____2796 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____2796
                                       then
                                         let uu____2816 =
                                           FStar_Syntax_Print.term_to_string
                                             w
                                            in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____2816
                                       else ());
                                      FStar_List.iter
                                        (fun g1  ->
                                           let uu____2823 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____2823
                                           then
                                             let uu____2824 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____2824
                                              then ()
                                              else
                                                (let uu____2826 =
                                                   let uu____2827 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____2827
                                                    in
                                                 failwith uu____2826))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___60_2830 =
                                           FStar_TypeChecker_Rel.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___60_2830.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___60_2830.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___60_2830.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         let uu____2832 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env2 g1
                                            in
                                         FStar_All.pipe_right uu____2832
                                           FStar_TypeChecker_Rel.resolve_implicits_tac
                                          in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s,ps1) ->
                                     ((let uu____2839 =
                                         let uu____2840 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____2840 ps1
                                          in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____2839 "at the time of failure");
                                      (let uu____2841 =
                                         let uu____2846 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s
                                            in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____2846)
                                          in
                                       FStar_Errors.raise_error uu____2841
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2856 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2860 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2864 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2913 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2949 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2999 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3037 . 'Auu____3037 -> 'Auu____3037 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3056 = FStar_Syntax_Util.head_and_args t  in
        match uu____3056 with
        | (hd1,args) ->
            let uu____3093 =
              let uu____3106 =
                let uu____3107 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3107.FStar_Syntax_Syntax.n  in
              (uu____3106, args)  in
            (match uu____3093 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3120))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3183 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3183 with
                       | (gs,uu____3191) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3198 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3198 with
                       | (gs,uu____3206) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3257 =
                        let uu____3264 =
                          let uu____3267 =
                            let uu____3268 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3268
                             in
                          [uu____3267]  in
                        (FStar_Syntax_Util.t_true, uu____3264)  in
                      Simplified uu____3257
                  | Both  ->
                      let uu____3279 =
                        let uu____3292 =
                          let uu____3295 =
                            let uu____3296 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3296
                             in
                          [uu____3295]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3292)  in
                      Dual uu____3279
                  | Neg  -> Simplified (assertion, []))
             | uu____3317 -> Unchanged t)
  
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
    fun uu___57_3397  ->
      match uu___57_3397 with
      | Unchanged t -> let uu____3403 = f t  in Unchanged uu____3403
      | Simplified (t,gs) ->
          let uu____3410 = let uu____3417 = f t  in (uu____3417, gs)  in
          Simplified uu____3410
      | Dual (tn,tp,gs) ->
          let uu____3427 =
            let uu____3436 = f tn  in
            let uu____3437 = f tp  in (uu____3436, uu____3437, gs)  in
          Dual uu____3427
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3491 = f t1 t2  in Unchanged uu____3491
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3503 = let uu____3510 = f t1 t2  in (uu____3510, gs)
               in
            Simplified uu____3503
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3524 = let uu____3531 = f t1 t2  in (uu____3531, gs)
               in
            Simplified uu____3524
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3550 =
              let uu____3557 = f t1 t2  in
              (uu____3557, (FStar_List.append gs1 gs2))  in
            Simplified uu____3550
        | uu____3560 ->
            let uu____3569 = explode x  in
            (match uu____3569 with
             | (n1,p1,gs1) ->
                 let uu____3587 = explode y  in
                 (match uu____3587 with
                  | (n2,p2,gs2) ->
                      let uu____3605 =
                        let uu____3614 = f n1 n2  in
                        let uu____3615 = f p1 p2  in
                        (uu____3614, uu____3615, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3605))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3680 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3680
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3723  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3757 =
              let uu____3758 = FStar_Syntax_Subst.compress t  in
              uu____3758.FStar_Syntax_Syntax.n  in
            match uu____3757 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3770 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3770 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3794 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3794 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3812;
                   FStar_Syntax_Syntax.vars = uu____3813;_},(p,uu____3815)::
                 (q,uu____3817)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3857 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3857
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3860 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3860 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3866 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3866.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3870;
                   FStar_Syntax_Syntax.vars = uu____3871;_},(p,uu____3873)::
                 (q,uu____3875)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3915 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3915
                   in
                let xq =
                  let uu____3917 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3917
                   in
                let r1 =
                  let uu____3919 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3919 p  in
                let r2 =
                  let uu____3921 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3921 q  in
                (match (r1, r2) with
                 | (Unchanged uu____3924,Unchanged uu____3925) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3935 = FStar_Syntax_Util.mk_iff l r  in
                            uu____3935.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3938 ->
                     let uu____3943 = explode r1  in
                     (match uu____3943 with
                      | (pn,pp,gs1) ->
                          let uu____3961 = explode r2  in
                          (match uu____3961 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3982 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____3983 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____3982
                                   uu____3983
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4035  ->
                       fun r  ->
                         match uu____4035 with
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
                let uu____4153 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4153 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4187  ->
                            match uu____4187 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4201 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___61_4225 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___61_4225.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___61_4225.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4201 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4245 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4245.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4291 = traverse f pol e t1  in
                let uu____4296 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4296 uu____4291
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___62_4334 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___62_4334.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___62_4334.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4341 =
                f pol e
                  (let uu___63_4345 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___63_4345.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___63_4345.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4341
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___64_4355 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___64_4355.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___64_4355.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4356 = explode rp  in
              (match uu____4356 with
               | (uu____4365,p',gs') ->
                   Dual
                     ((let uu___65_4379 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___65_4379.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___65_4379.FStar_Syntax_Syntax.vars)
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
      (let uu____4414 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4414);
      (let uu____4435 = FStar_ST.op_Bang tacdbg  in
       if uu____4435
       then
         let uu____4455 =
           let uu____4456 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4456
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4457 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4455
           uu____4457
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4486 =
         let uu____4493 = traverse by_tactic_interp Pos env goal  in
         match uu____4493 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4511 -> failwith "no"  in
       match uu____4486 with
       | (t',gs) ->
           ((let uu____4533 = FStar_ST.op_Bang tacdbg  in
             if uu____4533
             then
               let uu____4553 =
                 let uu____4554 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4554
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4555 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4553 uu____4555
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4602  ->
                    fun g  ->
                      match uu____4602 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4647 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____4647 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4650 =
                                  let uu____4651 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty
                                     in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4651
                                   in
                                failwith uu____4650
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4654 = FStar_ST.op_Bang tacdbg  in
                            if uu____4654
                            then
                              let uu____4674 = FStar_Util.string_of_int n1
                                 in
                              let uu____4675 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4674 uu____4675
                            else ());
                           (let gt' =
                              let uu____4678 =
                                let uu____4679 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4679
                                 in
                              FStar_TypeChecker_Util.label uu____4678
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____4694 = s1  in
             match uu____4694 with
             | (uu____4715,gs1) ->
                 let uu____4733 =
                   let uu____4740 = FStar_Options.peek ()  in
                   (env, t', uu____4740)  in
                 uu____4733 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4751 =
        let uu____4752 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4752  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4751 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4753 =
      let uu____4754 =
        let uu____4755 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4756 =
          let uu____4759 = FStar_Syntax_Syntax.as_arg a  in [uu____4759]  in
        uu____4755 :: uu____4756  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4754  in
    uu____4753 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4772 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____4772);
        (let uu____4792 =
           let uu____4799 = reify_tactic tau  in
           run_tactic_on_typ uu____4799 env typ  in
         match uu____4792 with
         | (gs,w) ->
             let uu____4806 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4810 =
                      let uu____4811 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____4811  in
                    Prims.op_Negation uu____4810) gs
                in
             if uu____4806
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
      (let uu____4826 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4826);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____4847 =
         let uu____4854 = reify_tactic tau  in
         run_tactic_on_typ uu____4854 env typ  in
       match uu____4847 with
       | (gs,w) ->
           ((let uu____4864 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4868 =
                      let uu____4869 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____4869  in
                    Prims.op_Negation uu____4868) gs
                in
             if uu____4864
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
             let uu____4874 =
               let uu____4879 =
                 FStar_Syntax_Embeddings.unembed_list
                   FStar_Reflection_Embeddings.unembed_sigelt
                  in
               uu____4879 w1  in
             FStar_All.pipe_left FStar_Util.must uu____4874)))
  