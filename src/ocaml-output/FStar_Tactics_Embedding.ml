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
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____35 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____35 
let (t_result : FStar_Syntax_Syntax.term) =
  let uu____36 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.tconst uu____36 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____44 = let uu____55 = FStar_Syntax_Syntax.as_arg t  in [uu____55]
       in
    FStar_Syntax_Util.mk_app t_result uu____44
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____80 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____80 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____81 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____81 
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____110 =
      let uu____111 = FStar_Syntax_Subst.compress t  in
      uu____111.FStar_Syntax_Syntax.n  in
    match uu____110 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ->
        let uu____117 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____117
    | uu____120 ->
        (if w
         then
           (let uu____122 =
              let uu____127 =
                let uu____128 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s" uu____128
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____127)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____122)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_proofstate unembed_proofstate
    t_proofstate
  
let (unfold_lazy_proofstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_string "(((proofstate)))" 
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate ps =
    let li =
      let uu____144 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____144;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.typ = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    FStar_TypeChecker_NBETerm.Lazy li  in
  let unembed_proofstate t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy li when
        li.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ->
        let uu____156 = FStar_Dyn.undyn li.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____156
    | uu____159 -> FStar_Pervasives_Native.None  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ =
      (FStar_TypeChecker_NBETerm.FV (fv_proofstate, [], []))
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result rng res =
      match res with
      | FStar_Tactics_Result.Failed (msg,ps) ->
          let uu____207 =
            let uu____212 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____213 =
              let uu____214 =
                let uu____223 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____223  in
              let uu____224 =
                let uu____235 =
                  let uu____244 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string rng msg
                     in
                  FStar_Syntax_Syntax.as_arg uu____244  in
                let uu____245 =
                  let uu____256 =
                    let uu____265 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____265  in
                  [uu____256]  in
                uu____235 :: uu____245  in
              uu____214 :: uu____224  in
            FStar_Syntax_Syntax.mk_Tm_app uu____212 uu____213  in
          uu____207 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____302 =
            let uu____307 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____308 =
              let uu____309 =
                let uu____318 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____318  in
              let uu____319 =
                let uu____330 =
                  let uu____339 = FStar_Syntax_Embeddings.embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____339  in
                let uu____340 =
                  let uu____351 =
                    let uu____360 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____360  in
                  [uu____351]  in
                uu____330 :: uu____340  in
              uu____309 :: uu____319  in
            FStar_Syntax_Syntax.mk_Tm_app uu____307 uu____308  in
          uu____302 FStar_Pervasives_Native.None rng
       in
    let unembed_result w t =
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm  in
        let uu____435 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____435 with
        | (hd1,args) ->
            let uu____492 =
              let uu____493 = FStar_Syntax_Util.un_uinst hd1  in
              uu____493.FStar_Syntax_Syntax.n  in
            (uu____492, args)
         in
      let uu____506 = hd'_and_args t  in
      match uu____506 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____528)::(ps,uu____530)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____597 = FStar_Syntax_Embeddings.unembed' w ea a  in
          FStar_Util.bind_opt uu____597
            (fun a1  ->
               let uu____605 =
                 FStar_Syntax_Embeddings.unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____605
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(msg,uu____617)::(ps,uu____619)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____686 =
            FStar_Syntax_Embeddings.unembed' w
              FStar_Syntax_Embeddings.e_string msg
             in
          FStar_Util.bind_opt uu____686
            (fun msg1  ->
               let uu____694 =
                 FStar_Syntax_Embeddings.unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____694
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (msg1, ps1))))
      | uu____703 ->
          (if w
           then
             (let uu____719 =
                let uu____724 =
                  let uu____725 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____725
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____724)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____719)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____729 =
      let uu____730 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____730  in
    FStar_Syntax_Embeddings.mk_emb embed_result unembed_result uu____729
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____761 =
      let uu____762 = FStar_Syntax_Subst.compress t  in
      uu____762.FStar_Syntax_Syntax.n  in
    match uu____761 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____769 ->
        (if w
         then
           (let uu____771 =
              let uu____776 =
                let uu____777 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____777
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____776)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____771)
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
    let uu____807 =
      let uu____808 = FStar_Syntax_Subst.compress t  in
      uu____808.FStar_Syntax_Syntax.n  in
    match uu____807 with
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
    | uu____817 ->
        (if w
         then
           (let uu____819 =
              let uu____824 =
                let uu____825 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____825
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____824)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____819)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_guard_policy unembed_guard_policy
    t_guard_policy
  