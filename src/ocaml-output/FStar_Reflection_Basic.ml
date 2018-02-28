open Prims
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____4 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____4 FStar_Syntax_Syntax.fv_to_tm
  
let (fstar_refl_embed : FStar_Syntax_Syntax.term) =
  lid_as_tm FStar_Parser_Const.fstar_refl_embed_lid 
let (protect_embedded_term :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun x  ->
      let uu____13 =
        let uu____14 =
          let uu____15 = FStar_Syntax_Syntax.iarg t  in
          let uu____16 =
            let uu____19 = FStar_Syntax_Syntax.as_arg x  in [uu____19]  in
          uu____15 :: uu____16  in
        FStar_Syntax_Syntax.mk_Tm_app fstar_refl_embed uu____14  in
      uu____13 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos
  
let (un_protect_embedded_term :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____29 =
      let uu____44 = FStar_Syntax_Util.unmeta t  in
      FStar_Syntax_Util.head_and_args uu____44  in
    match uu____29 with
    | (head1,args) ->
        let uu____69 =
          let uu____82 =
            let uu____83 = FStar_Syntax_Util.un_uinst head1  in
            uu____83.FStar_Syntax_Syntax.n  in
          (uu____82, args)  in
        (match uu____69 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____97::(x,uu____99)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_refl_embed_lid
             -> FStar_Pervasives_Native.Some x
         | uu____138 ->
             ((let uu____152 =
                 let uu____157 =
                   let uu____158 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.format1 "Not an protected term: %s" uu____158
                    in
                 (FStar_Errors.Warning_UnprotectedTerm, uu____157)  in
               FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____152);
              FStar_Pervasives_Native.None))
  
let (embed_binder :
  FStar_Range.range -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun b  ->
      FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_binder b
        "reflection.embed_binder" (FStar_Pervasives_Native.Some rng)
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    try
      let uu____184 =
        let uu____185 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____185 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____184
    with
    | uu____192 ->
        ((let uu____194 =
            let uu____199 =
              let uu____200 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____200  in
            (FStar_Errors.Warning_NotEmbedded, uu____199)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____194);
         FStar_Pervasives_Native.None)
  
let (embed_binders :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun l  ->
      let uu____210 =
        FStar_Syntax_Embeddings.embed_list embed_binder
          FStar_Reflection_Data.fstar_refl_binder
         in
      uu____210 rng l
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____225 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____225 t
  
let (embed_term :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun t  ->
      let t1 = protect_embedded_term FStar_Syntax_Syntax.tun t  in
      let uu___57_244 = t1  in
      {
        FStar_Syntax_Syntax.n = (uu___57_244.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___57_244.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_term :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun t  -> un_protect_embedded_term t 
let (embed_fvar :
  FStar_Range.range -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun fv  ->
      FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_fvar fv
        "reflection.embed_fvar" (FStar_Pervasives_Native.Some rng)
  
let (unembed_fvar :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    try
      let uu____281 =
        let uu____282 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____282 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____281
    with
    | uu____289 ->
        ((let uu____291 =
            let uu____296 =
              let uu____297 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____297  in
            (FStar_Errors.Warning_NotEmbedded, uu____296)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____291);
         FStar_Pervasives_Native.None)
  
let (embed_comp :
  FStar_Range.range -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_comp c
        "reflection.embed_comp" (FStar_Pervasives_Native.Some rng)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    try
      let uu____323 =
        let uu____324 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____324 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____323
    with
    | uu____331 ->
        ((let uu____333 =
            let uu____338 =
              let uu____339 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____339  in
            (FStar_Errors.Warning_NotEmbedded, uu____338)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____333);
         FStar_Pervasives_Native.None)
  
let (embed_env :
  FStar_Range.range -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun env  ->
      FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_env env
        "tactics_embed_env" (FStar_Pervasives_Native.Some rng)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    try
      let uu____365 =
        let uu____366 = FStar_Syntax_Util.un_alien t  in
        FStar_All.pipe_right uu____366 FStar_Dyn.undyn  in
      FStar_Pervasives_Native.Some uu____365
    with
    | uu____373 ->
        ((let uu____375 =
            let uu____380 =
              let uu____381 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____381  in
            (FStar_Errors.Warning_NotEmbedded, uu____380)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____375);
         FStar_Pervasives_Native.None)
  
let (embed_const :
  FStar_Range.range ->
    FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      let r =
        match c with
        | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
        | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
        | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
        | FStar_Reflection_Data.C_Int i ->
            let uu____393 =
              let uu____394 =
                let uu____395 =
                  let uu____396 =
                    let uu____397 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____397  in
                  FStar_Syntax_Syntax.as_arg uu____396  in
                [uu____395]  in
              FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
                uu____394
               in
            uu____393 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____401 =
              let uu____402 =
                let uu____403 =
                  let uu____404 = FStar_Syntax_Embeddings.embed_string rng s
                     in
                  FStar_Syntax_Syntax.as_arg uu____404  in
                [uu____403]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String uu____402
               in
            uu____401 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___64_407 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___64_407.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___64_407.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____418 = FStar_Syntax_Util.head_and_args t1  in
    match uu____418 with
    | (hd1,args) ->
        let uu____457 =
          let uu____470 =
            let uu____471 = FStar_Syntax_Util.un_uinst hd1  in
            uu____471.FStar_Syntax_Syntax.n  in
          (uu____470, args)  in
        (match uu____457 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_True_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_False_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____531)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____556 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____556
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____565)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____590 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____590
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____597 ->
             ((let uu____611 =
                 let uu____616 =
                   let uu____617 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____617
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____616)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____611);
              FStar_Pervasives_Native.None))
  
let rec (embed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedder) =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____626 =
            let uu____627 =
              let uu____628 =
                let uu____629 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____629  in
              [uu____628]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant uu____627
             in
          uu____626 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____638 =
            let uu____639 =
              let uu____640 =
                let uu____641 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____641  in
              let uu____642 =
                let uu____645 =
                  let uu____646 =
                    let uu____647 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern
                       in
                    uu____647 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____646  in
                [uu____645]  in
              uu____640 :: uu____642  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
              uu____639
             in
          uu____638 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____658 =
            let uu____659 =
              let uu____660 =
                let uu____661 =
                  let uu____662 = FStar_Syntax_Syntax.mk_binder bv  in
                  embed_binder rng uu____662  in
                FStar_Syntax_Syntax.as_arg uu____661  in
              [uu____660]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
              uu____659
             in
          uu____658 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____666 =
            let uu____667 =
              let uu____668 =
                let uu____669 =
                  let uu____670 = FStar_Syntax_Syntax.mk_binder bv  in
                  embed_binder rng uu____670  in
                FStar_Syntax_Syntax.as_arg uu____669  in
              [uu____668]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
              uu____667
             in
          uu____666 FStar_Pervasives_Native.None rng
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____681 = FStar_Syntax_Util.head_and_args t1  in
    match uu____681 with
    | (hd1,args) ->
        let uu____720 =
          let uu____733 =
            let uu____734 = FStar_Syntax_Util.un_uinst hd1  in
            uu____734.FStar_Syntax_Syntax.n  in
          (uu____733, args)  in
        (match uu____720 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____749)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____774 = unembed_const c  in
             FStar_Util.bind_opt uu____774
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____783)::(ps,uu____785)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____820 = unembed_fvar f  in
             FStar_Util.bind_opt uu____820
               (fun f1  ->
                  let uu____826 =
                    let uu____831 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____831 ps  in
                  FStar_Util.bind_opt uu____826
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____850)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____875 = unembed_binder b  in
             FStar_Util.bind_opt uu____875
               (fun uu____881  ->
                  match uu____881 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                        (FStar_Reflection_Data.Pat_Var bv))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____890)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____915 = unembed_binder b  in
             FStar_Util.bind_opt uu____915
               (fun uu____921  ->
                  match uu____921 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                        (FStar_Reflection_Data.Pat_Wild bv))
         | uu____928 ->
             ((let uu____942 =
                 let uu____947 =
                   let uu____948 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s" uu____948
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____947)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____942);
              FStar_Pervasives_Native.None))
  
let (embed_branch :
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedder)
  =
  FStar_Syntax_Embeddings.embed_pair embed_pattern
    FStar_Reflection_Data.fstar_refl_pattern embed_term
    FStar_Syntax_Syntax.t_term
  
let (unembed_branch :
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_pair unembed_pattern unembed_term 
let (embed_aqualv :
  FStar_Range.range ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun q  ->
      let r =
        match q with
        | FStar_Reflection_Data.Q_Explicit  ->
            FStar_Reflection_Data.ref_Q_Explicit
        | FStar_Reflection_Data.Q_Implicit  ->
            FStar_Reflection_Data.ref_Q_Implicit
         in
      let uu___65_981 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___65_981.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___65_981.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____992 = FStar_Syntax_Util.head_and_args t1  in
    match uu____992 with
    | (hd1,args) ->
        let uu____1031 =
          let uu____1044 =
            let uu____1045 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1045.FStar_Syntax_Syntax.n  in
          (uu____1044, args)  in
        (match uu____1031 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____1088 ->
             ((let uu____1102 =
                 let uu____1107 =
                   let uu____1108 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____1108
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1107)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1102);
              FStar_Pervasives_Native.None))
  
let (embed_argv :
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedder)
  =
  FStar_Syntax_Embeddings.embed_pair embed_term FStar_Syntax_Syntax.t_term
    embed_aqualv FStar_Reflection_Data.fstar_refl_aqualv
  
let (unembed_argv :
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_pair unembed_term unembed_aqualv 
let (embed_term_view :
  FStar_Range.range ->
    FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun t  ->
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1141 =
            let uu____1142 =
              let uu____1143 =
                let uu____1144 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1144  in
              [uu____1143]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
              uu____1142
             in
          uu____1141 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1148 =
            let uu____1149 =
              let uu____1150 =
                let uu____1151 = embed_binder rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1151  in
              [uu____1150]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
              uu____1149
             in
          uu____1148 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1156 =
            let uu____1157 =
              let uu____1158 =
                let uu____1159 = embed_term rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1159  in
              let uu____1160 =
                let uu____1163 =
                  let uu____1164 = embed_argv rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1164  in
                [uu____1163]  in
              uu____1158 :: uu____1160  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
              uu____1157
             in
          uu____1156 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1169 =
            let uu____1170 =
              let uu____1171 =
                let uu____1172 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1172  in
              let uu____1173 =
                let uu____1176 =
                  let uu____1177 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1177  in
                [uu____1176]  in
              uu____1171 :: uu____1173  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
              uu____1170
             in
          uu____1169 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1182 =
            let uu____1183 =
              let uu____1184 =
                let uu____1185 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1185  in
              let uu____1186 =
                let uu____1189 =
                  let uu____1190 = embed_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____1190  in
                [uu____1189]  in
              uu____1184 :: uu____1186  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
              uu____1183
             in
          uu____1182 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1194 =
            let uu____1195 =
              let uu____1196 =
                let uu____1197 = FStar_Syntax_Embeddings.embed_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____1197  in
              [uu____1196]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
              uu____1195
             in
          uu____1194 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1202 =
            let uu____1203 =
              let uu____1204 =
                let uu____1205 = embed_binder rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1205  in
              let uu____1206 =
                let uu____1209 =
                  let uu____1210 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1210  in
                [uu____1209]  in
              uu____1204 :: uu____1206  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
              uu____1203
             in
          uu____1202 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1214 =
            let uu____1215 =
              let uu____1216 =
                let uu____1217 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1217  in
              [uu____1216]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
              uu____1215
             in
          uu____1214 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____1222 =
            let uu____1223 =
              let uu____1224 =
                let uu____1225 = FStar_Syntax_Embeddings.embed_int rng u  in
                FStar_Syntax_Syntax.as_arg uu____1225  in
              let uu____1226 =
                let uu____1229 =
                  let uu____1230 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1230  in
                [uu____1229]  in
              uu____1224 :: uu____1226  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
              uu____1223
             in
          uu____1222 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
          let uu____1236 =
            let uu____1237 =
              let uu____1238 =
                let uu____1239 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____1239  in
              let uu____1240 =
                let uu____1243 =
                  let uu____1244 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1244  in
                let uu____1245 =
                  let uu____1248 =
                    let uu____1249 = embed_term rng t2  in
                    FStar_Syntax_Syntax.as_arg uu____1249  in
                  [uu____1248]  in
                uu____1243 :: uu____1245  in
              uu____1238 :: uu____1240  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Let
              uu____1237
             in
          uu____1236 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1258 =
            let uu____1259 =
              let uu____1260 =
                let uu____1261 = embed_term rng t1  in
                FStar_Syntax_Syntax.as_arg uu____1261  in
              let uu____1262 =
                let uu____1265 =
                  let uu____1266 =
                    let uu____1267 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch
                       in
                    uu____1267 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____1266  in
                [uu____1265]  in
              uu____1260 :: uu____1262  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
              uu____1259
             in
          uu____1258 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___66_1285 = FStar_Reflection_Data.ref_Tv_Unknown  in
          {
            FStar_Syntax_Syntax.n = (uu___66_1285.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___66_1285.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_term_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1296 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1296 with
    | (hd1,args) ->
        let uu____1335 =
          let uu____1348 =
            let uu____1349 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1349.FStar_Syntax_Syntax.n  in
          (uu____1348, args)  in
        (match uu____1335 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1364)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1389 = unembed_binder b  in
             FStar_Util.bind_opt uu____1389
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1398)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1423 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1423
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1432)::(r,uu____1434)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1469 = unembed_term l  in
             FStar_Util.bind_opt uu____1469
               (fun l1  ->
                  let uu____1475 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1475
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1500)::(t2,uu____1502)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1537 = unembed_binder b  in
             FStar_Util.bind_opt uu____1537
               (fun b1  ->
                  let uu____1543 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1543
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1552)::(t2,uu____1554)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1589 = unembed_binder b  in
             FStar_Util.bind_opt uu____1589
               (fun b1  ->
                  let uu____1595 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1595
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1604)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             let uu____1629 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1629
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1638)::(t2,uu____1640)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1675 = unembed_binder b  in
             FStar_Util.bind_opt uu____1675
               (fun b1  ->
                  let uu____1681 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1681
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1690)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1715 = unembed_const c  in
             FStar_Util.bind_opt uu____1715
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1724)::(t2,uu____1726)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1761 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1761
               (fun u1  ->
                  let uu____1767 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1767
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1776)::(t11,uu____1778)::(t2,uu____1780)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let_lid
             ->
             let uu____1825 = unembed_binder b  in
             FStar_Util.bind_opt uu____1825
               (fun b1  ->
                  let uu____1831 = unembed_term t11  in
                  FStar_Util.bind_opt uu____1831
                    (fun t12  ->
                       let uu____1837 = unembed_term t2  in
                       FStar_Util.bind_opt uu____1837
                         (fun t21  ->
                            FStar_All.pipe_left
                              (fun _0_55  ->
                                 FStar_Pervasives_Native.Some _0_55)
                              (FStar_Reflection_Data.Tv_Let (b1, t12, t21)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1846)::(brs,uu____1848)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1883 = unembed_term t2  in
             FStar_Util.bind_opt uu____1883
               (fun t3  ->
                  let uu____1889 =
                    let uu____1898 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____1898 brs  in
                  FStar_Util.bind_opt uu____1889
                    (fun brs1  ->
                       FStar_All.pipe_left
                         (fun _0_56  -> FStar_Pervasives_Native.Some _0_56)
                         (FStar_Reflection_Data.Tv_Match (t3, brs1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             ->
             FStar_All.pipe_left
               (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
               FStar_Reflection_Data.Tv_Unknown
         | uu____1952 ->
             ((let uu____1966 =
                 let uu____1971 =
                   let uu____1972 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____1972
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1971)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1966);
              FStar_Pervasives_Native.None))
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total t ->
          let uu____1983 =
            let uu____1984 =
              let uu____1985 =
                let uu____1986 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____1986  in
              [uu____1985]  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Total
              uu____1984
             in
          uu____1983 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____1994 =
            let uu____1995 =
              let uu____1996 =
                let uu____1997 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____1997  in
              let uu____1998 =
                let uu____2001 =
                  let uu____2002 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____2002  in
                [uu____2001]  in
              uu____1996 :: uu____1998  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Lemma
              uu____1995
             in
          uu____1994 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___67_2005 = FStar_Reflection_Data.ref_C_Unknown  in
          {
            FStar_Syntax_Syntax.n = (uu___67_2005.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___67_2005.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2016 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2016 with
    | (hd1,args) ->
        let uu____2055 =
          let uu____2068 =
            let uu____2069 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2069.FStar_Syntax_Syntax.n  in
          (uu____2068, args)  in
        (match uu____2055 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____2084)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total_lid
             ->
             let uu____2109 = unembed_term t2  in
             FStar_Util.bind_opt uu____2109
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2118)::(post,uu____2120)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma_lid
             ->
             let uu____2155 = unembed_term pre  in
             FStar_Util.bind_opt uu____2155
               (fun pre1  ->
                  let uu____2161 = unembed_term post  in
                  FStar_Util.bind_opt uu____2161
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_59  -> FStar_Pervasives_Native.Some _0_59)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown_lid
             ->
             FStar_All.pipe_left
               (fun _0_60  -> FStar_Pervasives_Native.Some _0_60)
               FStar_Reflection_Data.C_Unknown
         | uu____2185 ->
             ((let uu____2199 =
                 let uu____2204 =
                   let uu____2205 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2205
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2204)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2199);
              FStar_Pervasives_Native.None))
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____2219::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____2244 = init xs  in x :: uu____2244
  
let (inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv  ->
    let uu____2254 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____2254
  
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns  ->
    let uu____2262 = FStar_Parser_Const.p2l ns  in
    FStar_Syntax_Syntax.lid_as_fv uu____2262
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
  
let (inspect_bv : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b) 
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____2270) ->
        let uu____2283 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____2283
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____2285) ->
        FStar_Reflection_Data.C_String s
    | uu____2286 ->
        let uu____2287 =
          let uu____2288 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____2288  in
        failwith uu____2287
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____2295) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2301 = FStar_Syntax_Syntax.mk_binder bv  in
        FStar_Reflection_Data.Tv_Var uu____2301
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2344 = last args  in
        (match uu____2344 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____2364) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit
                in
             let uu____2365 =
               let uu____2370 =
                 let uu____2373 =
                   let uu____2374 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2374  in
                 uu____2373 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos
                  in
               (uu____2370, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____2365)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2393,uu____2394) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____2436 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____2436 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2463 =
                    let uu____2468 = FStar_Syntax_Util.abs bs2 t4 k  in
                    (b, uu____2468)  in
                  FStar_Reflection_Data.Tv_Abs uu____2463))
    | FStar_Syntax_Syntax.Tm_type uu____2473 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____2489 ->
        let uu____2502 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____2502 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____2526 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____2526 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2555 -> failwith "impossible"  in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2565 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____2565
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____2592 =
          let uu____2597 =
            let uu____2598 = FStar_Syntax_Unionfind.uvar_id u  in
            FStar_BigInt.of_int_fs uu____2598  in
          (uu____2597, t3)  in
        FStar_Reflection_Data.Tv_Uvar uu____2592
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2618 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____2621 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____2621 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____2650 ->
                          failwith
                            "impossible: open_term returned different amount of binders"
                       in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2708 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____2708
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2727 =
                let uu____2734 =
                  FStar_List.map
                    (fun uu____2746  ->
                       match uu____2746 with
                       | (p1,uu____2754) -> inspect_pat p1) ps
                   in
                (fv, uu____2734)  in
              FStar_Reflection_Data.Pat_Cons uu____2727
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2763 ->
              failwith "NYI: Pat_dot_term"
           in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
        let brs2 =
          FStar_List.map
            (fun uu___53_2807  ->
               match uu___53_2807 with
               | (pat,uu____2829,t4) ->
                   let uu____2847 = inspect_pat pat  in (uu____2847, t4))
            brs1
           in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2860 ->
        ((let uu____2862 =
            let uu____2867 =
              let uu____2868 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____2869 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____2868
                uu____2869
               in
            (FStar_Errors.Warning_CantInspect, uu____2867)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____2862);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2874) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2885)::(post,uu____2887)::uu____2888 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2921 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____2931 ->
        FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____2944 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2949 =
          let uu____2960 = FStar_BigInt.string_of_big_int i  in
          (uu____2960, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____2949
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2976) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2985 =
               let uu____2994 = FStar_Syntax_Syntax.as_arg r  in [uu____2994]
                in
             FStar_Syntax_Util.mk_app l uu____2985
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2995 =
               let uu____3004 = FStar_Syntax_Syntax.iarg r  in [uu____3004]
                in
             FStar_Syntax_Util.mk_app l uu____2995)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____3010),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____3017 =
          let uu____3020 =
            let uu____3021 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____3021  in
          FStar_Syntax_Syntax.mk uu____3020  in
        uu____3017 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____3027 = FStar_BigInt.to_int_fs u  in
        FStar_Syntax_Util.uvar_from_id uu____3027 t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b  in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            []
           in
        let uu____3035 =
          let uu____3038 =
            let uu____3039 =
              let uu____3052 = FStar_Syntax_Subst.close [b] t2  in
              ((false, [lb]), uu____3052)  in
            FStar_Syntax_Syntax.Tm_let uu____3039  in
          FStar_Syntax_Syntax.mk uu____3038  in
        uu____3035 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____3081 =
                let uu____3082 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____3082  in
              FStar_All.pipe_left wrap uu____3081
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____3091 =
                let uu____3092 =
                  let uu____3105 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____3119 = pack_pat p1  in (uu____3119, false))
                      ps
                     in
                  (fv, uu____3105)  in
                FStar_Syntax_Syntax.Pat_cons uu____3092  in
              FStar_All.pipe_left wrap uu____3091
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
           in
        let brs1 =
          FStar_List.map
            (fun uu___54_3165  ->
               match uu___54_3165 with
               | (pat,t1) ->
                   let uu____3182 = pack_pat pat  in
                   (uu____3182, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        failwith "pack: unexpected term view"
  
let (embed_order :
  FStar_Range.range -> FStar_Order.order -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun o  ->
      let r =
        match o with
        | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
        | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
        | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt  in
      let uu___68_3204 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___68_3204.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___68_3204.FStar_Syntax_Syntax.vars)
      }
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3215 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3215 with
    | (hd1,args) ->
        let uu____3254 =
          let uu____3267 =
            let uu____3268 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3268.FStar_Syntax_Syntax.n  in
          (uu____3267, args)  in
        (match uu____3254 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Lt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Eq_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Gt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Gt
         | uu____3326 ->
             ((let uu____3340 =
                 let uu____3345 =
                   let uu____3346 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____3346
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3345)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3340);
              FStar_Pervasives_Native.None))
  
let (compare_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder -> FStar_Order.order)
  =
  fun x  ->
    fun y  ->
      let n1 =
        FStar_Syntax_Syntax.order_bv (FStar_Pervasives_Native.fst x)
          (FStar_Pervasives_Native.fst y)
         in
      if n1 < (Prims.parse_int "0")
      then FStar_Order.Lt
      else
        if n1 = (Prims.parse_int "0") then FStar_Order.Eq else FStar_Order.Gt
  
let (is_free :
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun x  ->
    fun t  -> FStar_Syntax_Util.is_free_in (FStar_Pervasives_Native.fst x) t
  
let (lookup_typ :
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list -> FStar_Reflection_Data.sigelt_view)
  =
  fun env  ->
    fun ns  ->
      let lid = FStar_Parser_Const.p2l ns  in
      let res = FStar_TypeChecker_Env.lookup_qname env lid  in
      match res with
      | FStar_Pervasives_Native.None  -> FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____3392,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____3493,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1  in
               let ctor1 dc_lid =
                 let uu____3510 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid  in
                 match uu____3510 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____3563,n1,uu____3565) ->
                          let uu____3570 =
                            let uu____3575 = FStar_Ident.path_of_lid lid2  in
                            (uu____3575, t1)  in
                          FStar_Reflection_Data.Ctor uu____3570
                      | uu____3580 -> failwith "wat 1")
                 | uu____3581 -> failwith "wat 2"  in
               let ctors = FStar_List.map ctor1 dc_lids  in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3590) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____3605 ->
                     failwith "global Sig_let has bv"
                  in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____3610 -> FStar_Reflection_Data.Unk)
  
let (embed_ctor :
  FStar_Range.range -> FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      match c with
      | FStar_Reflection_Data.Ctor (nm,t) ->
          let uu____3622 =
            let uu____3623 =
              let uu____3624 =
                let uu____3625 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____3625  in
              let uu____3626 =
                let uu____3629 =
                  let uu____3630 = embed_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____3630  in
                [uu____3629]  in
              uu____3624 :: uu____3626  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
              uu____3623
             in
          uu____3622 FStar_Pervasives_Native.None rng
  
let (unembed_ctor :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.ctor FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3643 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3643 with
    | (hd1,args) ->
        let uu____3682 =
          let uu____3695 =
            let uu____3696 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3696.FStar_Syntax_Syntax.n  in
          (uu____3695, args)  in
        (match uu____3682 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3711)::(t2,uu____3713)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____3748 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3748
               (fun nm1  ->
                  let uu____3760 = unembed_term t2  in
                  FStar_Util.bind_opt uu____3760
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                         (FStar_Reflection_Data.Ctor (nm1, t3))))
         | uu____3769 ->
             ((let uu____3783 =
                 let uu____3788 =
                   let uu____3789 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded ctor: %s" uu____3789
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____3788)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3783);
              FStar_Pervasives_Native.None))
  
let (embed_sigelt_view :
  FStar_Range.range ->
    FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun sev  ->
      match sev with
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____3811 =
            let uu____3812 =
              let uu____3813 =
                let uu____3814 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____3814  in
              let uu____3815 =
                let uu____3818 =
                  let uu____3819 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____3819  in
                let uu____3820 =
                  let uu____3823 =
                    let uu____3824 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3824  in
                  let uu____3825 =
                    let uu____3828 =
                      let uu____3829 =
                        let uu____3830 =
                          FStar_Syntax_Embeddings.embed_list embed_ctor
                            FStar_Reflection_Data.fstar_refl_ctor
                           in
                        uu____3830 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____3829  in
                    [uu____3828]  in
                  uu____3823 :: uu____3825  in
                uu____3818 :: uu____3820  in
              uu____3813 :: uu____3815  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive uu____3812
             in
          uu____3811 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
          let uu____3843 =
            let uu____3844 =
              let uu____3845 =
                let uu____3846 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____3846  in
              let uu____3847 =
                let uu____3850 =
                  let uu____3851 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____3851  in
                let uu____3852 =
                  let uu____3855 =
                    let uu____3856 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3856  in
                  [uu____3855]  in
                uu____3850 :: uu____3852  in
              uu____3845 :: uu____3847  in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Let
              uu____3844
             in
          uu____3843 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___69_3859 = FStar_Reflection_Data.ref_Unk  in
          {
            FStar_Syntax_Syntax.n = (uu___69_3859.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___69_3859.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3870 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3870 with
    | (hd1,args) ->
        let uu____3909 =
          let uu____3922 =
            let uu____3923 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3923.FStar_Syntax_Syntax.n  in
          (uu____3922, args)  in
        (match uu____3909 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3938)::(bs,uu____3940)::(t2,uu____3942)::(dcs,uu____3944)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3999 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____3999
               (fun nm1  ->
                  let uu____4011 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____4011
                    (fun bs1  ->
                       let uu____4017 = unembed_term t2  in
                       FStar_Util.bind_opt uu____4017
                         (fun t3  ->
                            let uu____4023 =
                              let uu____4028 =
                                FStar_Syntax_Embeddings.unembed_list
                                  unembed_ctor
                                 in
                              uu____4028 dcs  in
                            FStar_Util.bind_opt uu____4023
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____4049)::(ty,uu____4051)::(t2,uu____4053)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let_lid
             ->
             let uu____4098 = unembed_fvar fvar1  in
             FStar_Util.bind_opt uu____4098
               (fun fvar2  ->
                  let uu____4104 = unembed_term ty  in
                  FStar_Util.bind_opt uu____4104
                    (fun ty1  ->
                       let uu____4110 = unembed_term t2  in
                       FStar_Util.bind_opt uu____4110
                         (fun t3  ->
                            FStar_All.pipe_left
                              (fun _0_63  ->
                                 FStar_Pervasives_Native.Some _0_63)
                              (FStar_Reflection_Data.Sg_Let (fvar2, ty1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____4132 ->
             ((let uu____4146 =
                 let uu____4151 =
                   let uu____4152 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____4152
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____4151)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4146);
              FStar_Pervasives_Native.None))
  
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (type_of_binder : FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.typ)
  = fun b  -> match b with | (b1,uu____4160) -> b1.FStar_Syntax_Syntax.sort 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____4167 = FStar_Syntax_Util.un_uinst t1  in
      let uu____4168 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____4167 uu____4168
  
let (fresh_binder : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.binder) =
  fun t  ->
    let uu____4172 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t  in
    (uu____4172, FStar_Pervasives_Native.None)
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 