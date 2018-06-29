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
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"] 
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____42 = let uu____53 = FStar_Syntax_Syntax.as_arg t  in [uu____53]
       in
    FStar_Syntax_Util.mk_app t_result uu____42
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____78 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____78 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____79 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____79 
let mk_emb :
  'a .
    (FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
        -> FStar_Syntax_Syntax.term -> 'a FStar_Syntax_Embeddings.embedding
  =
  fun em  ->
    fun un  ->
      fun t  ->
        let uu____130 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____130
  
let embed :
  'Auu____176 .
    'Auu____176 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____176 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____196 = FStar_Syntax_Embeddings.embed e x  in
        uu____196 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____236 .
    Prims.bool ->
      'Auu____236 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____236 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____258 = FStar_Syntax_Embeddings.unembed e x  in
        uu____258 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____297 =
      let uu____298 = FStar_Syntax_Subst.compress t  in
      uu____298.FStar_Syntax_Syntax.n  in
    match uu____297 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____304;
          FStar_Syntax_Syntax.rng = uu____305;_}
        ->
        let uu____308 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____308
    | uu____311 ->
        (if w
         then
           (let uu____313 =
              let uu____318 =
                let uu____319 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s" uu____319
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____318)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____313)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_proofstate unembed_proofstate t_proofstate 
let (unfold_lazy_proofstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_string "(((proofstate)))" 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____386 uu____387 =
      match res with
      | FStar_Tactics_Result.Failed (msg,ps) ->
          let uu____413 =
            let uu____418 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____419 =
              let uu____420 =
                let uu____429 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____429  in
              let uu____430 =
                let uu____441 =
                  let uu____450 =
                    embed FStar_Syntax_Embeddings.e_string rng msg  in
                  FStar_Syntax_Syntax.as_arg uu____450  in
                let uu____451 =
                  let uu____462 =
                    let uu____471 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____471  in
                  [uu____462]  in
                uu____441 :: uu____451  in
              uu____420 :: uu____430  in
            FStar_Syntax_Syntax.mk_Tm_app uu____418 uu____419  in
          uu____413 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____508 =
            let uu____513 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____514 =
              let uu____515 =
                let uu____524 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____524  in
              let uu____525 =
                let uu____536 =
                  let uu____545 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____545  in
                let uu____546 =
                  let uu____557 =
                    let uu____566 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____566  in
                  [uu____557]  in
                uu____536 :: uu____546  in
              uu____515 :: uu____525  in
            FStar_Syntax_Syntax.mk_Tm_app uu____513 uu____514  in
          uu____508 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____622 =
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm  in
        let uu____650 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____650 with
        | (hd1,args) ->
            let uu____707 =
              let uu____708 = FStar_Syntax_Util.un_uinst hd1  in
              uu____708.FStar_Syntax_Syntax.n  in
            (uu____707, args)
         in
      let uu____721 = hd'_and_args t  in
      match uu____721 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____743)::(ps,uu____745)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____812 = unembed' w ea a  in
          FStar_Util.bind_opt uu____812
            (fun a1  ->
               let uu____820 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____820
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(msg,uu____832)::(ps,uu____834)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____901 = unembed' w FStar_Syntax_Embeddings.e_string msg  in
          FStar_Util.bind_opt uu____901
            (fun msg1  ->
               let uu____909 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____909
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (msg1, ps1))))
      | uu____918 ->
          (if w
           then
             (let uu____934 =
                let uu____939 =
                  let uu____940 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____940
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____939)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____934)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____944 =
      let uu____945 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____945  in
    let uu____946 =
      let uu____947 =
        let uu____954 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____955 =
          let uu____958 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____958]  in
        (uu____954, uu____955)  in
      FStar_Syntax_Syntax.ET_app uu____947  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result uu____944
      (fun uu____964  -> "") uu____946
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____995 =
      let uu____996 = FStar_Syntax_Subst.compress t  in
      uu____996.FStar_Syntax_Syntax.n  in
    match uu____995 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____1003 ->
        (if w
         then
           (let uu____1005 =
              let uu____1010 =
                let uu____1011 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____1011
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1010)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1005)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_direction unembed_direction t_direction 
let (e_guard_policy :
  FStar_Tactics_Types.guard_policy FStar_Syntax_Embeddings.embedding) =
  let embed_guard_policy rng p =
    match p with
    | FStar_Tactics_Types.SMT  -> fstar_tactics_SMT
    | FStar_Tactics_Types.Goal  -> fstar_tactics_Goal
    | FStar_Tactics_Types.Force  -> fstar_tactics_Force
    | FStar_Tactics_Types.Drop  -> fstar_tactics_Drop  in
  let unembed_guard_policy w t =
    let uu____1041 =
      let uu____1042 = FStar_Syntax_Subst.compress t  in
      uu____1042.FStar_Syntax_Syntax.n  in
    match uu____1041 with
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
    | uu____1051 ->
        (if w
         then
           (let uu____1053 =
              let uu____1058 =
                let uu____1059 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____1059
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1058)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1053)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_guard_policy unembed_guard_policy t_guard_policy 