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
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun s  ->
      let uu____33 =
        let uu____34 =
          let uu____35 = lid_as_tm FStar_Parser_Const.lid_tuple2  in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____35
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
           in
        let uu____36 =
          let uu____37 = FStar_Syntax_Syntax.as_arg t  in
          let uu____38 =
            let uu____41 = FStar_Syntax_Syntax.as_arg s  in [uu____41]  in
          uu____37 :: uu____38  in
        FStar_Syntax_Syntax.mk_Tm_app uu____34 uu____36  in
      uu____33 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (embed_proofstate :
  FStar_Range.range ->
    FStar_Tactics_Types.proofstate -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun ps  ->
      FStar_Syntax_Util.mk_alien t_proofstate ps "tactics.embed_proofstate"
        (FStar_Pervasives_Native.Some rng)
  
let (unembed_proofstate :
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Types.proofstate FStar_Pervasives_Native.option)
  =
  fun t  ->
    try
      let uu____64 =
        let uu____65 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____65 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____64
    with
    | uu____72 ->
        ((let uu____74 =
            let uu____79 =
              let uu____80 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded proofstate: %s" uu____80
               in
            (FStar_Errors.Warning_NotEmbedded, uu____79)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____74);
         FStar_Pervasives_Native.None)
  
let embed_result :
  'a .
    'a FStar_Syntax_Embeddings.embedder ->
      FStar_Reflection_Data.typ ->
        FStar_Range.range ->
          'a FStar_Tactics_Result.__result -> FStar_Syntax_Syntax.term
  =
  fun embed_a  ->
    fun t_a  ->
      fun rng  ->
        fun res  ->
          match res with
          | FStar_Tactics_Result.Failed (msg,ps) ->
              let uu____122 =
                let uu____123 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                    [FStar_Syntax_Syntax.U_zero]
                   in
                let uu____124 =
                  let uu____125 = FStar_Syntax_Syntax.iarg t_a  in
                  let uu____126 =
                    let uu____129 =
                      let uu____130 =
                        let uu____131 =
                          let uu____132 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero]
                             in
                          let uu____133 =
                            let uu____134 =
                              FStar_Syntax_Syntax.iarg
                                FStar_Syntax_Syntax.t_string
                               in
                            let uu____135 =
                              let uu____138 =
                                FStar_Syntax_Syntax.iarg t_proofstate  in
                              let uu____139 =
                                let uu____142 =
                                  let uu____143 =
                                    FStar_Syntax_Embeddings.embed_string rng
                                      msg
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____143  in
                                let uu____144 =
                                  let uu____147 =
                                    let uu____148 = embed_proofstate rng ps
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____148  in
                                  [uu____147]  in
                                uu____142 :: uu____144  in
                              uu____138 :: uu____139  in
                            uu____134 :: uu____135  in
                          FStar_Syntax_Syntax.mk_Tm_app uu____132 uu____133
                           in
                        uu____131 FStar_Pervasives_Native.None rng  in
                      FStar_Syntax_Syntax.as_arg uu____130  in
                    [uu____129]  in
                  uu____125 :: uu____126  in
                FStar_Syntax_Syntax.mk_Tm_app uu____123 uu____124  in
              uu____122 FStar_Pervasives_Native.None rng
          | FStar_Tactics_Result.Success (a,ps) ->
              let uu____155 =
                let uu____156 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                    [FStar_Syntax_Syntax.U_zero]
                   in
                let uu____157 =
                  let uu____158 = FStar_Syntax_Syntax.iarg t_a  in
                  let uu____159 =
                    let uu____162 =
                      let uu____163 =
                        let uu____164 =
                          let uu____165 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero]
                             in
                          let uu____166 =
                            let uu____167 = FStar_Syntax_Syntax.iarg t_a  in
                            let uu____168 =
                              let uu____171 =
                                FStar_Syntax_Syntax.iarg t_proofstate  in
                              let uu____172 =
                                let uu____175 =
                                  let uu____176 = embed_a rng a  in
                                  FStar_Syntax_Syntax.as_arg uu____176  in
                                let uu____180 =
                                  let uu____183 =
                                    let uu____184 = embed_proofstate rng ps
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____184  in
                                  [uu____183]  in
                                uu____175 :: uu____180  in
                              uu____171 :: uu____172  in
                            uu____167 :: uu____168  in
                          FStar_Syntax_Syntax.mk_Tm_app uu____165 uu____166
                           in
                        uu____164 FStar_Pervasives_Native.None rng  in
                      FStar_Syntax_Syntax.as_arg uu____163  in
                    [uu____162]  in
                  uu____158 :: uu____159  in
                FStar_Syntax_Syntax.mk_Tm_app uu____156 uu____157  in
              uu____155 FStar_Pervasives_Native.None rng
  
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
        let uu____240 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____240 with
        | (hd1,args) ->
            let uu____289 =
              let uu____290 = FStar_Syntax_Util.un_uinst hd1  in
              uu____290.FStar_Syntax_Syntax.n  in
            (uu____289, args)
         in
      let uu____301 = hd'_and_args t  in
      match uu____301 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____331)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____368 =
            let uu____375 =
              FStar_Syntax_Embeddings.unembed_pair unembed_a
                unembed_proofstate
               in
            uu____375 tuple2  in
          FStar_Util.bind_opt uu____368
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inl x))
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____433)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____470 =
            let uu____477 =
              FStar_Syntax_Embeddings.unembed_pair
                FStar_Syntax_Embeddings.unembed_string unembed_proofstate
               in
            uu____477 tuple2  in
          FStar_Util.bind_opt uu____470
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inr x))
      | uu____528 ->
          ((let uu____542 =
              let uu____547 =
                let uu____548 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded tactic result: %s"
                  uu____548
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____547)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____542);
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
    let uu____574 =
      let uu____575 = FStar_Syntax_Subst.compress t  in
      uu____575.FStar_Syntax_Syntax.n  in
    match uu____574 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____582 ->
        ((let uu____584 =
            let uu____589 =
              let uu____590 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____590
               in
            (FStar_Errors.Warning_NotEmbedded, uu____589)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____584);
         FStar_Pervasives_Native.None)
  