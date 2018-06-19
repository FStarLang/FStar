open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____15 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____15 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____21 = fstar_tactics_lid' ["Effect"; s]  in lid_as_tm uu____21
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____27 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
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
    let uu____43 = let uu____54 = FStar_Syntax_Syntax.as_arg t  in [uu____54]
       in
    FStar_Syntax_Util.mk_app t_result uu____43
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____79 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____79 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____80 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____80 
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____109 =
      let uu____110 = FStar_Syntax_Subst.compress t  in
      uu____110.FStar_Syntax_Syntax.n  in
    match uu____109 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ->
        let uu____116 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____116
    | uu____119 ->
        (if w
         then
           (let uu____121 =
              let uu____126 =
                let uu____127 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s" uu____127
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____126)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____121)
         else ();
         FStar_Pervasives_Native.None)
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
          let uu____169 =
            let uu____174 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____175 =
              let uu____176 =
                let uu____185 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____185  in
              let uu____186 =
                let uu____197 =
                  let uu____206 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string rng msg
                     in
                  FStar_Syntax_Syntax.as_arg uu____206  in
                let uu____207 =
                  let uu____218 =
                    let uu____227 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____227  in
                  [uu____218]  in
                uu____197 :: uu____207  in
              uu____176 :: uu____186  in
            FStar_Syntax_Syntax.mk_Tm_app uu____174 uu____175  in
          uu____169 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____264 =
            let uu____269 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____270 =
              let uu____271 =
                let uu____280 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____280  in
              let uu____281 =
                let uu____292 =
                  let uu____301 = FStar_Syntax_Embeddings.embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____301  in
                let uu____302 =
                  let uu____313 =
                    let uu____322 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____322  in
                  [uu____313]  in
                uu____292 :: uu____302  in
              uu____271 :: uu____281  in
            FStar_Syntax_Syntax.mk_Tm_app uu____269 uu____270  in
          uu____264 FStar_Pervasives_Native.None rng
       in
    let unembed_result w t =
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm  in
        let uu____397 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____397 with
        | (hd1,args) ->
            let uu____454 =
              let uu____455 = FStar_Syntax_Util.un_uinst hd1  in
              uu____455.FStar_Syntax_Syntax.n  in
            (uu____454, args)
         in
      let uu____468 = hd'_and_args t  in
      match uu____468 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____490)::(ps,uu____492)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____559 = FStar_Syntax_Embeddings.unembed' w ea a  in
          FStar_Util.bind_opt uu____559
            (fun a1  ->
               let uu____567 =
                 FStar_Syntax_Embeddings.unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____567
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(msg,uu____579)::(ps,uu____581)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____648 =
            FStar_Syntax_Embeddings.unembed' w
              FStar_Syntax_Embeddings.e_string msg
             in
          FStar_Util.bind_opt uu____648
            (fun msg1  ->
               let uu____656 =
                 FStar_Syntax_Embeddings.unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____656
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (msg1, ps1))))
      | uu____665 ->
          (if w
           then
             (let uu____681 =
                let uu____686 =
                  let uu____687 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____687
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____686)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____681)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____691 =
      let uu____692 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____692  in
    FStar_Syntax_Embeddings.mk_emb embed_result unembed_result uu____691
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____723 =
      let uu____724 = FStar_Syntax_Subst.compress t  in
      uu____724.FStar_Syntax_Syntax.n  in
    match uu____723 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____731 ->
        (if w
         then
           (let uu____733 =
              let uu____738 =
                let uu____739 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____739
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____738)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____733)
         else ();
         FStar_Pervasives_Native.None)
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
    let uu____769 =
      let uu____770 = FStar_Syntax_Subst.compress t  in
      uu____770.FStar_Syntax_Syntax.n  in
    match uu____769 with
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
    | uu____779 ->
        (if w
         then
           (let uu____781 =
              let uu____786 =
                let uu____787 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____787
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____786)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____781)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_guard_policy unembed_guard_policy
    t_guard_policy
  