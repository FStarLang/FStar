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
  
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____32 = lid_as_data_fv l  in FStar_Syntax_Syntax.fv_to_tm uu____32
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____38 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____38
  
let (fstar_tactics_Failed_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Result"; "Failed"] 
let (fstar_tactics_Success_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Result"; "Success"] 
let (fstar_tactics_Failed_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Failed_lid 
let (fstar_tactics_Success_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Success_lid 
let (fstar_tactics_Failed_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Failed_lid 
let (fstar_tactics_Success_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Success_lid 
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
  let uu____39 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____39 
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____40 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____40 
let (t_result : FStar_Syntax_Syntax.term) =
  let uu____41 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.tconst uu____41 
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____42 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.fvconst uu____42 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____50 = let uu____61 = FStar_Syntax_Syntax.as_arg t  in [uu____61]
       in
    FStar_Syntax_Util.mk_app t_result uu____50
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____86 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____86 
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____87 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.fvconst uu____87 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____88 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____88 
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____89 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.fvconst uu____89 
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____118 =
      let uu____119 = FStar_Syntax_Subst.compress t  in
      uu____119.FStar_Syntax_Syntax.n  in
    match uu____118 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ->
        let uu____125 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____125
    | uu____128 ->
        (if w
         then
           (let uu____130 =
              let uu____135 =
                let uu____136 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s" uu____136
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____135)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____130)
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
      let uu____152 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____152;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.typ = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    FStar_TypeChecker_NBETerm.Lazy li  in
  let unembed_proofstate t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy li when
        li.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ->
        let uu____164 = FStar_Dyn.undyn li.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____164
    | uu____167 ->
        ((let uu____169 =
            let uu____174 =
              let uu____175 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE proofstate: %s"
                uu____175
               in
            (FStar_Errors.Warning_NotEmbedded, uu____174)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____169);
         FStar_Pervasives_Native.None)
     in
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
          let uu____223 =
            let uu____228 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____229 =
              let uu____230 =
                let uu____239 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____239  in
              let uu____240 =
                let uu____251 =
                  let uu____260 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string rng msg
                     in
                  FStar_Syntax_Syntax.as_arg uu____260  in
                let uu____261 =
                  let uu____272 =
                    let uu____281 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____281  in
                  [uu____272]  in
                uu____251 :: uu____261  in
              uu____230 :: uu____240  in
            FStar_Syntax_Syntax.mk_Tm_app uu____228 uu____229  in
          uu____223 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____318 =
            let uu____323 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____324 =
              let uu____325 =
                let uu____334 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____334  in
              let uu____335 =
                let uu____346 =
                  let uu____355 = FStar_Syntax_Embeddings.embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____355  in
                let uu____356 =
                  let uu____367 =
                    let uu____376 =
                      FStar_Syntax_Embeddings.embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____376  in
                  [uu____367]  in
                uu____346 :: uu____356  in
              uu____325 :: uu____335  in
            FStar_Syntax_Syntax.mk_Tm_app uu____323 uu____324  in
          uu____318 FStar_Pervasives_Native.None rng
       in
    let unembed_result w t =
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm  in
        let uu____451 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____451 with
        | (hd1,args) ->
            let uu____508 =
              let uu____509 = FStar_Syntax_Util.un_uinst hd1  in
              uu____509.FStar_Syntax_Syntax.n  in
            (uu____508, args)
         in
      let uu____522 = hd'_and_args t  in
      match uu____522 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____544)::(ps,uu____546)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____613 = FStar_Syntax_Embeddings.unembed' w ea a  in
          FStar_Util.bind_opt uu____613
            (fun a1  ->
               let uu____621 =
                 FStar_Syntax_Embeddings.unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____621
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(msg,uu____633)::(ps,uu____635)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____702 =
            FStar_Syntax_Embeddings.unembed' w
              FStar_Syntax_Embeddings.e_string msg
             in
          FStar_Util.bind_opt uu____702
            (fun msg1  ->
               let uu____710 =
                 FStar_Syntax_Embeddings.unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____710
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (msg1, ps1))))
      | uu____719 ->
          (if w
           then
             (let uu____735 =
                let uu____740 =
                  let uu____741 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____741
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____740)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____735)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____745 =
      let uu____746 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____746  in
    FStar_Syntax_Embeddings.mk_emb embed_result unembed_result uu____745
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result res =
      match res with
      | FStar_Tactics_Result.Failed (msg,ps) ->
          let uu____779 =
            let uu____794 =
              let uu____801 =
                let uu____806 =
                  FStar_TypeChecker_NBETerm.embed e_proofstate_nbe ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____806  in
              let uu____807 =
                let uu____814 =
                  let uu____819 =
                    FStar_TypeChecker_NBETerm.embed
                      FStar_TypeChecker_NBETerm.e_string msg
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____819  in
                let uu____820 =
                  let uu____827 =
                    let uu____832 = FStar_TypeChecker_NBETerm.type_of ea  in
                    FStar_TypeChecker_NBETerm.as_iarg uu____832  in
                  [uu____827]  in
                uu____814 :: uu____820  in
              uu____801 :: uu____807  in
            (fstar_tactics_Failed_fv, [FStar_Syntax_Syntax.U_zero],
              uu____794)
             in
          FStar_TypeChecker_NBETerm.FV uu____779
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____859 =
            let uu____874 =
              let uu____881 =
                let uu____886 =
                  FStar_TypeChecker_NBETerm.embed e_proofstate_nbe ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____886  in
              let uu____887 =
                let uu____894 =
                  let uu____899 = FStar_TypeChecker_NBETerm.embed ea a  in
                  FStar_TypeChecker_NBETerm.as_arg uu____899  in
                let uu____900 =
                  let uu____907 =
                    let uu____912 = FStar_TypeChecker_NBETerm.type_of ea  in
                    FStar_TypeChecker_NBETerm.as_iarg uu____912  in
                  [uu____907]  in
                uu____894 :: uu____900  in
              uu____881 :: uu____887  in
            (fstar_tactics_Success_fv, [FStar_Syntax_Syntax.U_zero],
              uu____874)
             in
          FStar_TypeChecker_NBETerm.FV uu____859
       in
    let unembed_result t = FStar_Pervasives_Native.None  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ =
        (FStar_TypeChecker_NBETerm.FV (fv_result, [], []))
    }
  
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
  FStar_Syntax_Embeddings.mk_emb embed_direction unembed_direction
    t_direction
  
let (e_direction_nbe :
  FStar_Tactics_Types.direction FStar_TypeChecker_NBETerm.embedding) =
  let embed_direction res = failwith "e_direction_nbe"  in
  let unembed_direction t = FStar_Pervasives_Native.None  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ =
      (FStar_TypeChecker_NBETerm.FV (fv_direction, [], []))
  } 
let (e_guard_policy :
  FStar_Tactics_Types.guard_policy FStar_Syntax_Embeddings.embedding) =
  let embed_guard_policy rng p =
    match p with
    | FStar_Tactics_Types.SMT  -> fstar_tactics_SMT
    | FStar_Tactics_Types.Goal  -> fstar_tactics_Goal
    | FStar_Tactics_Types.Force  -> fstar_tactics_Force
    | FStar_Tactics_Types.Drop  -> fstar_tactics_Drop  in
  let unembed_guard_policy w t =
    let uu____1071 =
      let uu____1072 = FStar_Syntax_Subst.compress t  in
      uu____1072.FStar_Syntax_Syntax.n  in
    match uu____1071 with
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
    | uu____1081 ->
        (if w
         then
           (let uu____1083 =
              let uu____1088 =
                let uu____1089 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____1089
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1088)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1083)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_guard_policy unembed_guard_policy
    t_guard_policy
  
let (e_guard_policy_nbe :
  FStar_Tactics_Types.guard_policy FStar_TypeChecker_NBETerm.embedding) =
  let embed_guard_policy res = failwith "e_guard_policy_nbe"  in
  let unembed_guard_policy t = FStar_Pervasives_Native.None  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ =
      (FStar_TypeChecker_NBETerm.FV (fv_guard_policy, [], []))
  } 