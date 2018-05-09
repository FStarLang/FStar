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
    let uu____43 = let uu____52 = FStar_Syntax_Syntax.as_arg t  in [uu____52]
       in
    FStar_Syntax_Util.mk_app t_result uu____43
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____71 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____71 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____72 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____72 
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____101 =
      let uu____102 = FStar_Syntax_Subst.compress t  in
      uu____102.FStar_Syntax_Syntax.n  in
    match uu____101 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ->
        let uu____108 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____108
    | uu____111 ->
        (if w
         then
           (let uu____113 =
              let uu____118 =
                let uu____119 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s" uu____119
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____118)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____113)
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
          let uu____161 =
            let uu____166 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____167 =
              let uu____168 =
                let uu____175 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____175  in
              let uu____176 =
                let uu____185 =
                  let uu____192 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string rng msg
                     in
                  FStar_Syntax_Syntax.as_arg uu____192  in
                let uu____193 =
                  let uu____202 =
                    let uu____209 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____209  in
                  [uu____202]  in
                uu____185 :: uu____193  in
              uu____168 :: uu____176  in
            FStar_Syntax_Syntax.mk_Tm_app uu____166 uu____167  in
          uu____161 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____238 =
            let uu____243 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____244 =
              let uu____245 =
                let uu____252 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____252  in
              let uu____253 =
                let uu____262 =
                  let uu____269 = FStar_Syntax_Embeddings.embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____269  in
                let uu____270 =
                  let uu____279 =
                    let uu____286 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____286  in
                  [uu____279]  in
                uu____262 :: uu____270  in
              uu____245 :: uu____253  in
            FStar_Syntax_Syntax.mk_Tm_app uu____243 uu____244  in
          uu____238 FStar_Pervasives_Native.None rng
       in
    let unembed_result w t =
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm  in
        let uu____351 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____351 with
        | (hd1,args) ->
            let uu____400 =
              let uu____401 = FStar_Syntax_Util.un_uinst hd1  in
              uu____401.FStar_Syntax_Syntax.n  in
            (uu____400, args)
         in
      let uu____412 = hd'_and_args t  in
      match uu____412 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____432)::(ps,uu____434)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____481 = FStar_Syntax_Embeddings.unembed' w ea a  in
          FStar_Util.bind_opt uu____481
            (fun a1  ->
               let uu____489 =
                 FStar_Syntax_Embeddings.unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____489
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(msg,uu____501)::(ps,uu____503)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____550 =
            FStar_Syntax_Embeddings.unembed' w
              FStar_Syntax_Embeddings.e_string msg
             in
          FStar_Util.bind_opt uu____550
            (fun msg1  ->
               let uu____558 =
                 FStar_Syntax_Embeddings.unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____558
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (msg1, ps1))))
      | uu____567 ->
          (if w
           then
             (let uu____581 =
                let uu____586 =
                  let uu____587 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____587
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____586)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____581)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____591 =
      let uu____592 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____592  in
    FStar_Syntax_Embeddings.mk_emb embed_result unembed_result uu____591
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____623 =
      let uu____624 = FStar_Syntax_Subst.compress t  in
      uu____624.FStar_Syntax_Syntax.n  in
    match uu____623 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____631 ->
        (if w
         then
           (let uu____633 =
              let uu____638 =
                let uu____639 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____639
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____638)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____633)
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
    let uu____669 =
      let uu____670 = FStar_Syntax_Subst.compress t  in
      uu____670.FStar_Syntax_Syntax.n  in
    match uu____669 with
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
    | uu____679 ->
        (if w
         then
           (let uu____681 =
              let uu____686 =
                let uu____687 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____687
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____686)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____681)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_guard_policy unembed_guard_policy
    t_guard_policy
  