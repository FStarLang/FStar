open Prims
type name = FStar_Syntax_Syntax.bv[@@deriving show]
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____15 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____15 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____21 = fstar_tactics_lid' ["Effect"; s]  in lid_as_tm uu____21
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____27 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
       in
    FStar_Syntax_Syntax.fv_to_tm uu____27
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____33 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____33
  
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
let (t_proofstate : FStar_Syntax_Syntax.term) =
  let uu____34 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____34 
let (t_result : FStar_Syntax_Syntax.term) =
  let uu____35 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.tconst uu____35 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____43 = let uu____52 = FStar_Syntax_Syntax.as_arg t  in [uu____52]
       in
    FStar_Syntax_Util.mk_app t_result uu____43
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____53 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____53 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____54 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____54 
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____79 =
      let uu____80 = FStar_Syntax_Subst.compress t  in
      uu____80.FStar_Syntax_Syntax.n  in
    match uu____79 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ->
        let uu____86 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____86
    | uu____89 ->
        let uu____90 =
          if w
          then
            let uu____91 =
              let uu____96 =
                let uu____97 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s" uu____97
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____96)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____91
          else ()  in
        FStar_Pervasives_Native.None
     in
  FStar_Syntax_Embeddings.mk_emb embed_proofstate unembed_proofstate
    t_proofstate
  
let (unfold_lazy_proofstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_string "(((proofstate)))" 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result rng res =
      match res with
      | FStar_Tactics_Result.Failed (msg,ps) ->
          let uu____137 =
            let uu____140 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____141 =
              let uu____142 =
                let uu____143 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____143  in
              let uu____144 =
                let uu____147 =
                  let uu____148 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string rng msg
                     in
                  FStar_Syntax_Syntax.as_arg uu____148  in
                let uu____149 =
                  let uu____152 =
                    let uu____153 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____153  in
                  [uu____152]  in
                uu____147 :: uu____149  in
              uu____142 :: uu____144  in
            FStar_Syntax_Syntax.mk_Tm_app uu____140 uu____141  in
          uu____137 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____158 =
            let uu____161 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____162 =
              let uu____163 =
                let uu____164 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____164  in
              let uu____165 =
                let uu____168 =
                  let uu____169 = FStar_Syntax_Embeddings.embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____169  in
                let uu____170 =
                  let uu____173 =
                    let uu____174 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____174  in
                  [uu____173]  in
                uu____168 :: uu____170  in
              uu____163 :: uu____165  in
            FStar_Syntax_Syntax.mk_Tm_app uu____161 uu____162  in
          uu____158 FStar_Pervasives_Native.None rng
       in
    let unembed_result w t =
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm  in
        let uu____212 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____212 with
        | (hd1,args) ->
            let uu____261 =
              let uu____262 = FStar_Syntax_Util.un_uinst hd1  in
              uu____262.FStar_Syntax_Syntax.n  in
            (uu____261, args)
         in
      let uu____273 = hd'_and_args t  in
      match uu____273 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____293)::(ps,uu____295)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____342 = FStar_Syntax_Embeddings.unembed ea a  in
          FStar_Util.bind_opt uu____342
            (fun a1  ->
               let uu____350 =
                 FStar_Syntax_Embeddings.unembed e_proofstate ps  in
               FStar_Util.bind_opt uu____350
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(msg,uu____362)::(ps,uu____364)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____411 =
            FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_string
              msg
             in
          FStar_Util.bind_opt uu____411
            (fun msg1  ->
               let uu____419 =
                 FStar_Syntax_Embeddings.unembed e_proofstate ps  in
               FStar_Util.bind_opt uu____419
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (msg1, ps1))))
      | uu____428 ->
          let uu____441 =
            if w
            then
              let uu____442 =
                let uu____447 =
                  let uu____448 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____448
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____447)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____442
            else ()  in
          FStar_Pervasives_Native.None
       in
    let uu____452 =
      let uu____453 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____453  in
    FStar_Syntax_Embeddings.mk_emb embed_result unembed_result uu____452
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____480 =
      let uu____481 = FStar_Syntax_Subst.compress t  in
      uu____481.FStar_Syntax_Syntax.n  in
    match uu____480 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____488 ->
        let uu____489 =
          if w
          then
            let uu____490 =
              let uu____495 =
                let uu____496 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____496
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____495)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____490
          else ()  in
        FStar_Pervasives_Native.None
     in
  FStar_Syntax_Embeddings.mk_emb embed_direction unembed_direction
    t_direction
  
let (e_guard_policy :
  FStar_Tactics_Types.guard_policy FStar_Syntax_Embeddings.embedding) =
  let embed_guard_policy rng p =
    match p with
    | FStar_Tactics_Types.SMT  -> fstar_tactics_SMT
    | FStar_Tactics_Types.Goal  -> fstar_tactics_Goal
    | FStar_Tactics_Types.Force  -> fstar_tactics_Force
    | FStar_Tactics_Types.Drop  -> fstar_tactics_Drop  in
  let unembed_guard_policy w t =
    let uu____522 =
      let uu____523 = FStar_Syntax_Subst.compress t  in
      uu____523.FStar_Syntax_Syntax.n  in
    match uu____522 with
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
    | uu____532 ->
        let uu____533 =
          if w
          then
            let uu____534 =
              let uu____539 =
                let uu____540 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____540
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____539)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____534
          else ()  in
        FStar_Pervasives_Native.None
     in
  FStar_Syntax_Embeddings.mk_emb embed_guard_policy unembed_guard_policy
    t_guard_policy
  