open Prims
type name = FStar_Syntax_Syntax.bv[@@deriving show]
let fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____15 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____15 FStar_Syntax_Syntax.fv_to_tm
  
let mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____21 = fstar_tactics_lid' ["Effect"; s]  in lid_as_tm uu____21
  
let lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____27 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
       in
    FStar_Syntax_Syntax.fv_to_tm uu____27
  
let fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____33 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____33
  
let fstar_tactics_Failed_lid : FStar_Ident.lid =
  fstar_tactics_lid' ["Result"; "Failed"] 
let fstar_tactics_Success_lid : FStar_Ident.lid =
  fstar_tactics_lid' ["Result"; "Success"] 
let fstar_tactics_Failed_tm : FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_Failed_lid 
let fstar_tactics_Success_tm : FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_Success_lid 
let fstar_tactics_topdown_lid : FStar_Ident.lid =
  fstar_tactics_lid' ["Types"; "TopDown"] 
let fstar_tactics_bottomup_lid : FStar_Ident.lid =
  fstar_tactics_lid' ["Types"; "BottomUp"] 
let fstar_tactics_topdown : FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_topdown_lid 
let fstar_tactics_bottomup : FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_bottomup_lid 
let fstar_tactics_SMT_lid : FStar_Ident.lid =
  fstar_tactics_lid' ["Types"; "SMT"] 
let fstar_tactics_Goal_lid : FStar_Ident.lid =
  fstar_tactics_lid' ["Types"; "Goal"] 
let fstar_tactics_Drop_lid : FStar_Ident.lid =
  fstar_tactics_lid' ["Types"; "Drop"] 
let fstar_tactics_Force_lid : FStar_Ident.lid =
  fstar_tactics_lid' ["Types"; "Force"] 
let fstar_tactics_SMT : FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_SMT_lid 
let fstar_tactics_Goal : FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_Goal_lid 
let fstar_tactics_Drop : FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_Drop_lid 
let fstar_tactics_Force : FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_Force_lid 
let t_proofstate : FStar_Syntax_Syntax.term =
  let uu____34 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____34 
let t_result : FStar_Syntax_Syntax.term =
  let uu____35 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.tconst uu____35 
let t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let uu____43 = let uu____52 = FStar_Syntax_Syntax.as_arg t  in [uu____52]
       in
    FStar_Syntax_Util.mk_app t_result uu____43
  
let t_guard_policy : FStar_Syntax_Syntax.term =
  let uu____53 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____53 
let t_direction : FStar_Syntax_Syntax.term =
  let uu____54 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____54 
let e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____83 =
      let uu____84 = FStar_Syntax_Subst.compress t  in
      uu____84.FStar_Syntax_Syntax.n  in
    match uu____83 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ->
        let uu____90 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____90
    | uu____93 ->
        (if w
         then
           (let uu____95 =
              let uu____100 =
                let uu____101 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s" uu____101
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____100)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____95)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_proofstate unembed_proofstate
    t_proofstate
  
let unfold_lazy_proofstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term =
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
          let uu____143 =
            let uu____148 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____149 =
              let uu____150 =
                let uu____151 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____151  in
              let uu____152 =
                let uu____155 =
                  let uu____156 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string rng msg
                     in
                  FStar_Syntax_Syntax.as_arg uu____156  in
                let uu____157 =
                  let uu____160 =
                    let uu____161 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____161  in
                  [uu____160]  in
                uu____155 :: uu____157  in
              uu____150 :: uu____152  in
            FStar_Syntax_Syntax.mk_Tm_app uu____148 uu____149  in
          uu____143 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____166 =
            let uu____171 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____172 =
              let uu____173 =
                let uu____174 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____174  in
              let uu____175 =
                let uu____178 =
                  let uu____179 = FStar_Syntax_Embeddings.embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____179  in
                let uu____180 =
                  let uu____183 =
                    let uu____184 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____184  in
                  [uu____183]  in
                uu____178 :: uu____180  in
              uu____173 :: uu____175  in
            FStar_Syntax_Syntax.mk_Tm_app uu____171 uu____172  in
          uu____166 FStar_Pervasives_Native.None rng
       in
    let unembed_result w t =
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm  in
        let uu____225 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____225 with
        | (hd1,args) ->
            let uu____274 =
              let uu____275 = FStar_Syntax_Util.un_uinst hd1  in
              uu____275.FStar_Syntax_Syntax.n  in
            (uu____274, args)
         in
      let uu____286 = hd'_and_args t  in
      match uu____286 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____306)::(ps,uu____308)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____355 = FStar_Syntax_Embeddings.unembed ea a  in
          FStar_Util.bind_opt uu____355
            (fun a1  ->
               let uu____363 =
                 FStar_Syntax_Embeddings.unembed e_proofstate ps  in
               FStar_Util.bind_opt uu____363
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(msg,uu____375)::(ps,uu____377)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____424 =
            FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_string
              msg
             in
          FStar_Util.bind_opt uu____424
            (fun msg1  ->
               let uu____432 =
                 FStar_Syntax_Embeddings.unembed e_proofstate ps  in
               FStar_Util.bind_opt uu____432
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (msg1, ps1))))
      | uu____441 ->
          (if w
           then
             (let uu____455 =
                let uu____460 =
                  let uu____461 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____461
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____460)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____455)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____465 =
      let uu____466 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____466  in
    FStar_Syntax_Embeddings.mk_emb embed_result unembed_result uu____465
  
let e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____497 =
      let uu____498 = FStar_Syntax_Subst.compress t  in
      uu____498.FStar_Syntax_Syntax.n  in
    match uu____497 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____505 ->
        (if w
         then
           (let uu____507 =
              let uu____512 =
                let uu____513 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____513
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____512)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____507)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_direction unembed_direction
    t_direction
  
let e_guard_policy :
  FStar_Tactics_Types.guard_policy FStar_Syntax_Embeddings.embedding =
  let embed_guard_policy rng p =
    match p with
    | FStar_Tactics_Types.SMT  -> fstar_tactics_SMT
    | FStar_Tactics_Types.Goal  -> fstar_tactics_Goal
    | FStar_Tactics_Types.Force  -> fstar_tactics_Force
    | FStar_Tactics_Types.Drop  -> fstar_tactics_Drop  in
  let unembed_guard_policy w t =
    let uu____543 =
      let uu____544 = FStar_Syntax_Subst.compress t  in
      uu____544.FStar_Syntax_Syntax.n  in
    match uu____543 with
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
    | uu____553 ->
        (if w
         then
           (let uu____555 =
              let uu____560 =
                let uu____561 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____561
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____560)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____555)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_guard_policy unembed_guard_policy
    t_guard_policy
  