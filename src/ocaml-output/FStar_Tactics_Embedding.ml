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
let (fstar_tactics_SMT_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "SMT"] 
let (fstar_tactics_Goal_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Goal"] 
let (fstar_tactics_Drop_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Drop"] 
let (fstar_tactics_Force_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Force"] 
let (fstar_tactics_SMT : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_SMT_lid 
let (fstar_tactics_Goal : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Goal_lid 
let (fstar_tactics_Drop : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Drop_lid 
let (fstar_tactics_Force : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Force_lid 
let (mktuple2_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm FStar_Parser_Const.lid_Mktuple2 
let (t_proofstate : FStar_Syntax_Syntax.term) =
  let uu____24 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____24 
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____25 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____25 
let (pair_typ :
  FStar_Reflection_Data.typ ->
    FStar_Reflection_Data.typ -> FStar_Reflection_Data.typ)
  =
  fun t  ->
    fun s  ->
      let uu____32 =
        let uu____33 =
          let uu____34 = lid_as_tm FStar_Parser_Const.lid_tuple2  in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____34
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
           in
        let uu____35 =
          let uu____36 = FStar_Syntax_Syntax.as_arg t  in
          let uu____37 =
            let uu____40 = FStar_Syntax_Syntax.as_arg s  in [uu____40]  in
          uu____36 :: uu____37  in
        FStar_Syntax_Syntax.mk_Tm_app uu____33 uu____35  in
      uu____32 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
    let uu____61 =
      let uu____62 = FStar_Syntax_Subst.compress t  in
      uu____62.FStar_Syntax_Syntax.n  in
    match uu____61 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_proofstate ->
        let uu____68 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_40  -> FStar_Pervasives_Native.Some _0_40) uu____68
    | uu____71 ->
        ((let uu____73 =
            let uu____78 =
              let uu____79 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded proofstate: %s" uu____79
               in
            (FStar_Errors.Warning_NotEmbedded, uu____78)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____73);
         FStar_Pervasives_Native.None)
  
let (unfold_lazy_proofstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_string "(((proofstate)))" 
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
              let uu____126 =
                let uu____127 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                    [FStar_Syntax_Syntax.U_zero]
                   in
                let uu____128 =
                  let uu____129 = FStar_Syntax_Syntax.iarg t_a  in
                  let uu____130 =
                    let uu____133 =
                      let uu____134 =
                        let uu____135 =
                          let uu____136 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero]
                             in
                          let uu____137 =
                            let uu____138 =
                              FStar_Syntax_Syntax.iarg
                                FStar_Syntax_Syntax.t_string
                               in
                            let uu____139 =
                              let uu____142 =
                                FStar_Syntax_Syntax.iarg t_proofstate  in
                              let uu____143 =
                                let uu____146 =
                                  let uu____147 =
                                    FStar_Syntax_Embeddings.embed_string rng
                                      msg
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____147  in
                                let uu____148 =
                                  let uu____151 =
                                    let uu____152 = embed_proofstate rng ps
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____152  in
                                  [uu____151]  in
                                uu____146 :: uu____148  in
                              uu____142 :: uu____143  in
                            uu____138 :: uu____139  in
                          FStar_Syntax_Syntax.mk_Tm_app uu____136 uu____137
                           in
                        uu____135 FStar_Pervasives_Native.None rng  in
                      FStar_Syntax_Syntax.as_arg uu____134  in
                    [uu____133]  in
                  uu____129 :: uu____130  in
                FStar_Syntax_Syntax.mk_Tm_app uu____127 uu____128  in
              uu____126 FStar_Pervasives_Native.None rng
          | FStar_Tactics_Result.Success (a,ps) ->
              let uu____159 =
                let uu____160 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                    [FStar_Syntax_Syntax.U_zero]
                   in
                let uu____161 =
                  let uu____162 = FStar_Syntax_Syntax.iarg t_a  in
                  let uu____163 =
                    let uu____166 =
                      let uu____167 =
                        let uu____168 =
                          let uu____169 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero]
                             in
                          let uu____170 =
                            let uu____171 = FStar_Syntax_Syntax.iarg t_a  in
                            let uu____172 =
                              let uu____175 =
                                FStar_Syntax_Syntax.iarg t_proofstate  in
                              let uu____176 =
                                let uu____179 =
                                  let uu____180 = embed_a rng a  in
                                  FStar_Syntax_Syntax.as_arg uu____180  in
                                let uu____184 =
                                  let uu____187 =
                                    let uu____188 = embed_proofstate rng ps
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____188  in
                                  [uu____187]  in
                                uu____179 :: uu____184  in
                              uu____175 :: uu____176  in
                            uu____171 :: uu____172  in
                          FStar_Syntax_Syntax.mk_Tm_app uu____169 uu____170
                           in
                        uu____168 FStar_Pervasives_Native.None rng  in
                      FStar_Syntax_Syntax.as_arg uu____167  in
                    [uu____166]  in
                  uu____162 :: uu____163  in
                FStar_Syntax_Syntax.mk_Tm_app uu____160 uu____161  in
              uu____159 FStar_Pervasives_Native.None rng
  
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
        let uu____244 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____244 with
        | (hd1,args) ->
            let uu____293 =
              let uu____294 = FStar_Syntax_Util.un_uinst hd1  in
              uu____294.FStar_Syntax_Syntax.n  in
            (uu____293, args)
         in
      let uu____305 = hd'_and_args t  in
      match uu____305 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____335)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____372 =
            let uu____379 =
              FStar_Syntax_Embeddings.unembed_pair unembed_a
                unembed_proofstate
               in
            uu____379 tuple2  in
          FStar_Util.bind_opt uu____372
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inl x))
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____437)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____474 =
            let uu____481 =
              FStar_Syntax_Embeddings.unembed_pair
                FStar_Syntax_Embeddings.unembed_string unembed_proofstate
               in
            uu____481 tuple2  in
          FStar_Util.bind_opt uu____474
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inr x))
      | uu____532 ->
          ((let uu____546 =
              let uu____551 =
                let uu____552 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded tactic result: %s"
                  uu____552
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____551)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____546);
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
    let uu____583 =
      let uu____584 = FStar_Syntax_Subst.compress t  in
      uu____584.FStar_Syntax_Syntax.n  in
    match uu____583 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____591 ->
        ((let uu____593 =
            let uu____598 =
              let uu____599 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____599
               in
            (FStar_Errors.Warning_NotEmbedded, uu____598)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____593);
         FStar_Pervasives_Native.None)
  
let (embed_guard_policy :
  FStar_Range.range ->
    FStar_Tactics_Types.guard_policy -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Tactics_Types.SMT  -> fstar_tactics_SMT
      | FStar_Tactics_Types.Goal  -> fstar_tactics_Goal
      | FStar_Tactics_Types.Force  -> fstar_tactics_Force
      | FStar_Tactics_Types.Drop  -> fstar_tactics_Drop
  
let (unembed_guard_policy :
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Types.guard_policy FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____618 =
      let uu____619 = FStar_Syntax_Subst.compress t  in
      uu____619.FStar_Syntax_Syntax.n  in
    match uu____618 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____628 ->
        ((let uu____630 =
            let uu____635 =
              let uu____636 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded guard_policy: %s" uu____636
               in
            (FStar_Errors.Warning_NotEmbedded, uu____635)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____630);
         FStar_Pervasives_Native.None)
  