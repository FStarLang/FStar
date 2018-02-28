open Prims
type name = FStar_Syntax_Syntax.bv[@@deriving show]
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____11 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____11 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____15 = fstar_tactics_lid' ["Effect"; s]  in lid_as_tm uu____15
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____19 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
       in
    FStar_Syntax_Syntax.fv_to_tm uu____19
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____23 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____23
  
let (fstar_tactics_Failed_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Result"; "Failed"] 
let (fstar_tactics_Success_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Result"; "Success"] 
let (fstar_tactics_Failed_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Failed_lid 
let (fstar_tactics_Success_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Success_lid 
let (fstar_tactics_topdown_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "TopDown"] 
let (fstar_tactics_bottomup_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "BottomUp"] 
let (fstar_tactics_topdown : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_topdown_lid 
let (fstar_tactics_bottomup : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_bottomup_lid 
let (mktuple2_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm FStar_Parser_Const.lid_Mktuple2 
let (t_proofstate : FStar_Syntax_Syntax.term) =
  let uu____24 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____24 
let (pair_typ :
  FStar_Reflection_Data.typ ->
    FStar_Reflection_Data.typ -> FStar_Reflection_Data.typ)
  =
  fun t  ->
    fun s  ->
      let uu____31 =
        let uu____32 =
          let uu____33 = lid_as_tm FStar_Parser_Const.lid_tuple2  in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____33
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
           in
        let uu____34 =
          let uu____35 = FStar_Syntax_Syntax.as_arg t  in
          let uu____36 =
            let uu____39 = FStar_Syntax_Syntax.as_arg s  in [uu____39]  in
          uu____35 :: uu____36  in
        FStar_Syntax_Syntax.mk_Tm_app uu____32 uu____34  in
      uu____31 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (embed_proofstate :
  FStar_Range.range ->
    FStar_Tactics_Types.proofstate -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun ps  ->
      FStar_Syntax_Util.mk_lazy ps t_proofstate
        FStar_Syntax_Syntax.Lazy_proofstate
        (FStar_Pervasives_Native.Some rng)
  
let (unembed_proofstate :
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Types.proofstate FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____60 =
      let uu____61 = FStar_Syntax_Subst.compress t  in
      uu____61.FStar_Syntax_Syntax.n  in
    match uu____60 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_proofstate ->
        let uu____67 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_40  -> FStar_Pervasives_Native.Some _0_40) uu____67
    | uu____70 ->
        ((let uu____72 =
            let uu____77 =
              let uu____78 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded proofstate: %s" uu____78
               in
            (FStar_Errors.Warning_NotEmbedded, uu____77)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____72);
         FStar_Pervasives_Native.None)
  
let (unfold_lazy_proofstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> failwith "cannot unfold proofstate -- this shouldn't be needed" 
let embed_result :
  'a .
    'a FStar_Syntax_Embeddings.embedder ->
      FStar_Reflection_Data.typ ->
        'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedder
  =
  fun embed_a  ->
    fun t_a  ->
      fun rng  ->
        fun res  ->
          match res with
          | FStar_Tactics_Result.Failed (msg,ps) ->
              let uu____125 =
                let uu____126 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                    [FStar_Syntax_Syntax.U_zero]
                   in
                let uu____127 =
                  let uu____128 = FStar_Syntax_Syntax.iarg t_a  in
                  let uu____129 =
                    let uu____132 =
                      let uu____133 =
                        let uu____134 =
                          let uu____135 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero]
                             in
                          let uu____136 =
                            let uu____137 =
                              FStar_Syntax_Syntax.iarg
                                FStar_Syntax_Syntax.t_string
                               in
                            let uu____138 =
                              let uu____141 =
                                FStar_Syntax_Syntax.iarg t_proofstate  in
                              let uu____142 =
                                let uu____145 =
                                  let uu____146 =
                                    FStar_Syntax_Embeddings.embed_string rng
                                      msg
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____146  in
                                let uu____147 =
                                  let uu____150 =
                                    let uu____151 = embed_proofstate rng ps
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____151  in
                                  [uu____150]  in
                                uu____145 :: uu____147  in
                              uu____141 :: uu____142  in
                            uu____137 :: uu____138  in
                          FStar_Syntax_Syntax.mk_Tm_app uu____135 uu____136
                           in
                        uu____134 FStar_Pervasives_Native.None rng  in
                      FStar_Syntax_Syntax.as_arg uu____133  in
                    [uu____132]  in
                  uu____128 :: uu____129  in
                FStar_Syntax_Syntax.mk_Tm_app uu____126 uu____127  in
              uu____125 FStar_Pervasives_Native.None rng
          | FStar_Tactics_Result.Success (a,ps) ->
              let uu____158 =
                let uu____159 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                    [FStar_Syntax_Syntax.U_zero]
                   in
                let uu____160 =
                  let uu____161 = FStar_Syntax_Syntax.iarg t_a  in
                  let uu____162 =
                    let uu____165 =
                      let uu____166 =
                        let uu____167 =
                          let uu____168 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero]
                             in
                          let uu____169 =
                            let uu____170 = FStar_Syntax_Syntax.iarg t_a  in
                            let uu____171 =
                              let uu____174 =
                                FStar_Syntax_Syntax.iarg t_proofstate  in
                              let uu____175 =
                                let uu____178 =
                                  let uu____179 = embed_a rng a  in
                                  FStar_Syntax_Syntax.as_arg uu____179  in
                                let uu____183 =
                                  let uu____186 =
                                    let uu____187 = embed_proofstate rng ps
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____187  in
                                  [uu____186]  in
                                uu____178 :: uu____183  in
                              uu____174 :: uu____175  in
                            uu____170 :: uu____171  in
                          FStar_Syntax_Syntax.mk_Tm_app uu____168 uu____169
                           in
                        uu____167 FStar_Pervasives_Native.None rng  in
                      FStar_Syntax_Syntax.as_arg uu____166  in
                    [uu____165]  in
                  uu____161 :: uu____162  in
                FStar_Syntax_Syntax.mk_Tm_app uu____159 uu____160  in
              uu____158 FStar_Pervasives_Native.None rng
  
let unembed_result :
  'a .
    FStar_Syntax_Syntax.term ->
      'a FStar_Syntax_Embeddings.unembedder ->
        (('a,FStar_Tactics_Types.proofstate) FStar_Pervasives_Native.tuple2,
          (Prims.string,FStar_Tactics_Types.proofstate)
            FStar_Pervasives_Native.tuple2)
          FStar_Util.either FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm  in
        let uu____243 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____243 with
        | (hd1,args) ->
            let uu____292 =
              let uu____293 = FStar_Syntax_Util.un_uinst hd1  in
              uu____293.FStar_Syntax_Syntax.n  in
            (uu____292, args)
         in
      let uu____304 = hd'_and_args t  in
      match uu____304 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____334)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____371 =
            let uu____378 =
              FStar_Syntax_Embeddings.unembed_pair unembed_a
                unembed_proofstate
               in
            uu____378 tuple2  in
          FStar_Util.bind_opt uu____371
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inl x))
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____436)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____473 =
            let uu____480 =
              FStar_Syntax_Embeddings.unembed_pair
                FStar_Syntax_Embeddings.unembed_string unembed_proofstate
               in
            uu____480 tuple2  in
          FStar_Util.bind_opt uu____473
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inr x))
      | uu____531 ->
          ((let uu____545 =
              let uu____550 =
                let uu____551 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded tactic result: %s"
                  uu____551
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____550)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____545);
           FStar_Pervasives_Native.None)
  
let (embed_direction :
  FStar_Range.range ->
    FStar_Tactics_Types.direction -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun d  ->
      match d with
      | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
      | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup
  
let (unembed_direction :
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Types.direction FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____582 =
      let uu____583 = FStar_Syntax_Subst.compress t  in
      uu____583.FStar_Syntax_Syntax.n  in
    match uu____582 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____590 ->
        ((let uu____592 =
            let uu____597 =
              let uu____598 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____598
               in
            (FStar_Errors.Warning_NotEmbedded, uu____597)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____592);
         FStar_Pervasives_Native.None)
  