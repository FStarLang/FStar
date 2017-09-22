open Prims
type name = FStar_Syntax_Syntax.bv
let fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____13 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____13 FStar_Syntax_Syntax.fv_to_tm
  
let mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____18 = fstar_tactics_lid' ["Effect"; s]  in lid_as_tm uu____18
  
let lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____23 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
       in
    FStar_Syntax_Syntax.fv_to_tm uu____23
  
let fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____28 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____28
  
let fstar_tactics_Failed_lid : FStar_Ident.lid =
  fstar_tactics_lid' ["Result"; "Failed"] 
let fstar_tactics_Success_lid : FStar_Ident.lid =
  fstar_tactics_lid' ["Result"; "Success"] 
let fstar_tactics_Failed_tm : FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_Failed_lid 
let fstar_tactics_Success_tm : FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_Success_lid 
let pair_typ :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      let uu____39 =
        let uu____40 =
          let uu____41 = lid_as_tm FStar_Parser_Const.lid_tuple2  in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____41
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
           in
        let uu____42 =
          let uu____43 = FStar_Syntax_Syntax.as_arg t  in
          let uu____44 =
            let uu____47 = FStar_Syntax_Syntax.as_arg s  in [uu____47]  in
          uu____43 :: uu____44  in
        FStar_Syntax_Syntax.mk_Tm_app uu____40 uu____42  in
      uu____39 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let embed_proofstate :
  FStar_Tactics_Types.proofstate -> FStar_Syntax_Syntax.term =
  fun ps  ->
    FStar_Syntax_Util.mk_alien ps "tactics.embed_proofstate"
      FStar_Pervasives_Native.None
  
let unembed_proofstate :
  FStar_Tactics_Types.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Types.proofstate
  =
  fun ps  ->
    fun t  ->
      let uu____62 = FStar_Syntax_Util.un_alien t  in
      FStar_All.pipe_right uu____62 FStar_Dyn.undyn
  
let mk_app :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun hd1  ->
    fun args  ->
      FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
        FStar_Range.dummyRange
  
let mktuple2_tm : FStar_Syntax_Syntax.term =
  lid_as_data_tm FStar_Parser_Const.lid_Mktuple2 
let t_proofstate : FStar_Syntax_Syntax.term =
  let uu____73 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____73 
let embed_result :
  'a .
    FStar_Tactics_Types.proofstate ->
      'a FStar_Tactics_Result.__result ->
        ('a -> FStar_Syntax_Syntax.term) ->
          FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun res  ->
      fun embed_a  ->
        fun t_a  ->
          match res with
          | FStar_Tactics_Result.Failed (msg,ps1) ->
              let uu____112 =
                FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                  [FStar_Syntax_Syntax.U_zero]
                 in
              let uu____113 =
                let uu____114 = FStar_Syntax_Syntax.iarg t_a  in
                let uu____115 =
                  let uu____118 =
                    let uu____119 =
                      let uu____120 =
                        FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                          [FStar_Syntax_Syntax.U_zero;
                          FStar_Syntax_Syntax.U_zero]
                         in
                      let uu____121 =
                        let uu____122 =
                          FStar_Syntax_Syntax.iarg
                            FStar_Syntax_Syntax.t_string
                           in
                        let uu____123 =
                          let uu____126 =
                            FStar_Syntax_Syntax.iarg t_proofstate  in
                          let uu____127 =
                            let uu____130 =
                              let uu____131 =
                                FStar_Syntax_Embeddings.embed_string msg  in
                              FStar_Syntax_Syntax.as_arg uu____131  in
                            let uu____132 =
                              let uu____135 =
                                let uu____136 = embed_proofstate ps1  in
                                FStar_Syntax_Syntax.as_arg uu____136  in
                              [uu____135]  in
                            uu____130 :: uu____132  in
                          uu____126 :: uu____127  in
                        uu____122 :: uu____123  in
                      mk_app uu____120 uu____121  in
                    FStar_Syntax_Syntax.as_arg uu____119  in
                  [uu____118]  in
                uu____114 :: uu____115  in
              mk_app uu____112 uu____113
          | FStar_Tactics_Result.Success (a,ps1) ->
              let uu____139 =
                FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                  [FStar_Syntax_Syntax.U_zero]
                 in
              let uu____140 =
                let uu____141 = FStar_Syntax_Syntax.iarg t_a  in
                let uu____142 =
                  let uu____145 =
                    let uu____146 =
                      let uu____147 =
                        FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                          [FStar_Syntax_Syntax.U_zero;
                          FStar_Syntax_Syntax.U_zero]
                         in
                      let uu____148 =
                        let uu____149 = FStar_Syntax_Syntax.iarg t_a  in
                        let uu____150 =
                          let uu____153 =
                            FStar_Syntax_Syntax.iarg t_proofstate  in
                          let uu____154 =
                            let uu____157 =
                              let uu____158 = embed_a a  in
                              FStar_Syntax_Syntax.as_arg uu____158  in
                            let uu____159 =
                              let uu____162 =
                                let uu____163 = embed_proofstate ps1  in
                                FStar_Syntax_Syntax.as_arg uu____163  in
                              [uu____162]  in
                            uu____157 :: uu____159  in
                          uu____153 :: uu____154  in
                        uu____149 :: uu____150  in
                      mk_app uu____147 uu____148  in
                    FStar_Syntax_Syntax.as_arg uu____146  in
                  [uu____145]  in
                uu____141 :: uu____142  in
              mk_app uu____139 uu____140
  
let unembed_result :
  'a .
    FStar_Tactics_Types.proofstate ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term -> 'a) ->
          (('a,FStar_Tactics_Types.proofstate) FStar_Pervasives_Native.tuple2,
            (Prims.string,FStar_Tactics_Types.proofstate)
              FStar_Pervasives_Native.tuple2)
            FStar_Util.either
  =
  fun ps  ->
    fun res  ->
      fun unembed_a  ->
        let hd'_and_args tm =
          let tm1 = FStar_Syntax_Util.unascribe tm  in
          let uu____219 = FStar_Syntax_Util.head_and_args tm1  in
          match uu____219 with
          | (hd1,args) ->
              let uu____268 =
                let uu____269 = FStar_Syntax_Util.un_uinst hd1  in
                uu____269.FStar_Syntax_Syntax.n  in
              (uu____268, args)
           in
        let tuple2_elements tm =
          let uu____292 = hd'_and_args tm  in
          match uu____292 with
          | (FStar_Syntax_Syntax.Tm_fvar
             fv,_t1::_t2::(arg1,uu____317)::(arg2,uu____319)::[]) when
              FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.lid_Mktuple2
              -> (arg1, arg2)
          | uu____382 ->
              let uu____395 =
                let uu____396 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.format1 "Expected a two-elements tuple, got %s"
                  uu____396
                 in
              failwith uu____395
           in
        let uu____405 = hd'_and_args res  in
        match uu____405 with
        | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____433)::[]) when
            FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
            let uu____470 = tuple2_elements tuple2  in
            (match uu____470 with
             | (embedded_a,embedded_ps) ->
                 let uu____501 =
                   let uu____506 = unembed_a embedded_a  in
                   let uu____507 = unembed_proofstate ps embedded_ps  in
                   (uu____506, uu____507)  in
                 FStar_Util.Inl uu____501)
        | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____519)::[]) when
            FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
            let uu____556 = tuple2_elements tuple2  in
            (match uu____556 with
             | (embedded_msg,embedded_ps) ->
                 let uu____587 =
                   let uu____592 =
                     FStar_Syntax_Embeddings.unembed_string embedded_msg  in
                   let uu____593 = unembed_proofstate ps embedded_ps  in
                   (uu____592, uu____593)  in
                 FStar_Util.Inr uu____587)
        | uu____602 ->
            let uu____615 =
              let uu____616 = FStar_Syntax_Print.term_to_string res  in
              FStar_Util.format1
                "Expected Result.Success or Result.Failed applied to a single argument, got %s"
                uu____616
               in
            failwith uu____615
  