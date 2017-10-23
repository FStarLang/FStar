open Prims
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____5 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None in
    FStar_All.pipe_right uu____5 FStar_Syntax_Syntax.fv_to_tm
let fstar_refl_embed: FStar_Syntax_Syntax.term =
  lid_as_tm FStar_Parser_Const.fstar_refl_embed_lid
let protect_embedded_term:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      let uu____16 =
        let uu____17 =
          let uu____18 = FStar_Syntax_Syntax.iarg t in
          let uu____19 =
            let uu____22 = FStar_Syntax_Syntax.as_arg x in [uu____22] in
          uu____18 :: uu____19 in
        FStar_Syntax_Syntax.mk_Tm_app fstar_refl_embed uu____17 in
      uu____16 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos
let un_protect_embedded_term:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____33 =
      let uu____48 = FStar_Syntax_Util.unmeta t in
      FStar_Syntax_Util.head_and_args uu____48 in
    match uu____33 with
    | (head1,args) ->
        let uu____73 =
          let uu____86 =
            let uu____87 = FStar_Syntax_Util.un_uinst head1 in
            uu____87.FStar_Syntax_Syntax.n in
          (uu____86, args) in
        (match uu____73 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____101::(x,uu____103)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_refl_embed_lid
             -> FStar_Pervasives_Native.Some x
         | uu____142 ->
             ((let uu____156 =
                 let uu____157 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format1 "Not an protected term: %s" uu____157 in
               FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____156);
              FStar_Pervasives_Native.None))
let embed_binder:
  FStar_Range.range -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun b  ->
      FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_binder b
        "reflection.embed_binder" (FStar_Pervasives_Native.Some rng)
let unembed_binder:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____181 =
        let uu____182 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____182 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____181
    with
    | uu____189 ->
        ((let uu____191 =
            let uu____192 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded binder: %s" uu____192 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____191);
         FStar_Pervasives_Native.None)
let embed_binders:
  FStar_Range.range ->
    FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun l  ->
      let uu____205 =
        FStar_Syntax_Embeddings.embed_list embed_binder
          FStar_Reflection_Data.fstar_refl_binder in
      uu____205 rng l
let unembed_binders:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder Prims.list FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____221 = FStar_Syntax_Embeddings.unembed_list unembed_binder in
    uu____221 t
let embed_term:
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun t  ->
      let t1 = protect_embedded_term FStar_Syntax_Syntax.tun t in
      let uu___115_239 = t1 in
      {
        FStar_Syntax_Syntax.n = (uu___115_239.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___115_239.FStar_Syntax_Syntax.vars)
      }
let unembed_term:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  = fun t  -> un_protect_embedded_term t
let embed_fvar:
  FStar_Range.range -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun fv  ->
      FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_fvar fv
        "reflection.embed_fvar" (FStar_Pervasives_Native.Some rng)
let unembed_fvar:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____273 =
        let uu____274 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____274 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____273
    with
    | uu____281 ->
        ((let uu____283 =
            let uu____284 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded fvar: %s" uu____284 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____283);
         FStar_Pervasives_Native.None)
let embed_comp:
  FStar_Range.range -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun c  ->
      FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_comp c
        "reflection.embed_comp" (FStar_Pervasives_Native.Some rng)
let unembed_comp:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____308 =
        let uu____309 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____309 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____308
    with
    | uu____316 ->
        ((let uu____318 =
            let uu____319 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded comp: %s" uu____319 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____318);
         FStar_Pervasives_Native.None)
let embed_env:
  FStar_Range.range -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun env  ->
      FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_env env
        "tactics_embed_env" (FStar_Pervasives_Native.Some rng)
let unembed_env:
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____343 =
        let uu____344 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____344 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____343
    with
    | uu____351 ->
        ((let uu____353 =
            let uu____354 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded env: %s" uu____354 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____353);
         FStar_Pervasives_Native.None)
let embed_const:
  FStar_Range.range ->
    FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun c  ->
      let r =
        match c with
        | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
        | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
        | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
        | FStar_Reflection_Data.C_Int i ->
            let uu____365 =
              let uu____366 =
                let uu____367 =
                  let uu____368 =
                    let uu____369 = FStar_Util.string_of_int i in
                    FStar_Syntax_Util.exp_int uu____369 in
                  FStar_Syntax_Syntax.as_arg uu____368 in
                [uu____367] in
              FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
                uu____366 in
            uu____365 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____373 =
              let uu____374 =
                let uu____375 =
                  let uu____376 = FStar_Syntax_Embeddings.embed_string rng s in
                  FStar_Syntax_Syntax.as_arg uu____376 in
                [uu____375] in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String uu____374 in
            uu____373 FStar_Pervasives_Native.None FStar_Range.dummyRange in
      let uu___122_379 = r in
      {
        FStar_Syntax_Syntax.n = (uu___122_379.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___122_379.FStar_Syntax_Syntax.vars)
      }
let unembed_const:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____389 = FStar_Syntax_Util.head_and_args t1 in
    match uu____389 with
    | (hd1,args) ->
        let uu____428 =
          let uu____441 =
            let uu____442 = FStar_Syntax_Util.un_uinst hd1 in
            uu____442.FStar_Syntax_Syntax.n in
          (uu____441, args) in
        (match uu____428 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____502)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____527 = FStar_Syntax_Embeddings.unembed_int i in
             FStar_Util.bind_opt uu____527
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____536)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____561 = FStar_Syntax_Embeddings.unembed_string s in
             FStar_Util.bind_opt uu____561
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.C_String s1))
         | uu____568 ->
             ((let uu____582 =
                 let uu____583 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded vconst: %s" uu____583 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____582);
              FStar_Pervasives_Native.None))
let rec embed_pattern:
  FStar_Range.range ->
    FStar_Reflection_Data.pattern -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____593 =
            let uu____594 =
              let uu____595 =
                let uu____596 = embed_const rng c in
                FStar_Syntax_Syntax.as_arg uu____596 in
              [uu____595] in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant uu____594 in
          uu____593 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____605 =
            let uu____606 =
              let uu____607 =
                let uu____608 = embed_fvar rng fv in
                FStar_Syntax_Syntax.as_arg uu____608 in
              let uu____609 =
                let uu____612 =
                  let uu____613 =
                    let uu____614 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern in
                    uu____614 rng ps in
                  FStar_Syntax_Syntax.as_arg uu____613 in
                [uu____612] in
              uu____607 :: uu____609 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
              uu____606 in
          uu____605 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____625 =
            let uu____626 =
              let uu____627 =
                let uu____628 =
                  let uu____629 = FStar_Syntax_Syntax.mk_binder bv in
                  embed_binder rng uu____629 in
                FStar_Syntax_Syntax.as_arg uu____628 in
              [uu____627] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
              uu____626 in
          uu____625 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____633 =
            let uu____634 =
              let uu____635 =
                let uu____636 =
                  let uu____637 = FStar_Syntax_Syntax.mk_binder bv in
                  embed_binder rng uu____637 in
                FStar_Syntax_Syntax.as_arg uu____636 in
              [uu____635] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
              uu____634 in
          uu____633 FStar_Pervasives_Native.None rng
let rec unembed_pattern:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.pattern FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____649 = FStar_Syntax_Util.head_and_args t1 in
    match uu____649 with
    | (hd1,args) ->
        let uu____688 =
          let uu____701 =
            let uu____702 = FStar_Syntax_Util.un_uinst hd1 in
            uu____702.FStar_Syntax_Syntax.n in
          (uu____701, args) in
        (match uu____688 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____717)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____742 = unembed_const c in
             FStar_Util.bind_opt uu____742
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____751)::(ps,uu____753)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____788 = unembed_fvar f in
             FStar_Util.bind_opt uu____788
               (fun f1  ->
                  let uu____794 =
                    let uu____799 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern in
                    uu____799 ps in
                  FStar_Util.bind_opt uu____794
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____818)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____843 = unembed_binder b in
             FStar_Util.bind_opt uu____843
               (fun uu____849  ->
                  match uu____849 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                        (FStar_Reflection_Data.Pat_Var bv))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____858)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____883 = unembed_binder b in
             FStar_Util.bind_opt uu____883
               (fun uu____889  ->
                  match uu____889 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                        (FStar_Reflection_Data.Pat_Wild bv))
         | uu____896 ->
             ((let uu____910 =
                 let uu____911 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded pattern: %s" uu____911 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____910);
              FStar_Pervasives_Native.None))
let embed_branch:
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedder
  =
  FStar_Syntax_Embeddings.embed_pair embed_pattern
    FStar_Reflection_Data.fstar_refl_pattern embed_term
    FStar_Syntax_Syntax.t_term
let unembed_branch:
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder
  = FStar_Syntax_Embeddings.unembed_pair unembed_pattern unembed_term
let embed_aqualv:
  FStar_Range.range ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun q  ->
      let r =
        match q with
        | FStar_Reflection_Data.Q_Explicit  ->
            FStar_Reflection_Data.ref_Q_Explicit
        | FStar_Reflection_Data.Q_Implicit  ->
            FStar_Reflection_Data.ref_Q_Implicit in
      let uu___123_938 = r in
      {
        FStar_Syntax_Syntax.n = (uu___123_938.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___123_938.FStar_Syntax_Syntax.vars)
      }
let unembed_aqualv:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____948 = FStar_Syntax_Util.head_and_args t1 in
    match uu____948 with
    | (hd1,args) ->
        let uu____987 =
          let uu____1000 =
            let uu____1001 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1001.FStar_Syntax_Syntax.n in
          (uu____1000, args) in
        (match uu____987 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____1044 ->
             ((let uu____1058 =
                 let uu____1059 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded aqualv: %s" uu____1059 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____1058);
              FStar_Pervasives_Native.None))
let embed_argv:
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedder
  =
  FStar_Syntax_Embeddings.embed_pair embed_term FStar_Syntax_Syntax.t_term
    embed_aqualv FStar_Reflection_Data.fstar_refl_aqualv
let unembed_argv:
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder
  = FStar_Syntax_Embeddings.unembed_pair unembed_term unembed_aqualv
let embed_term_view:
  FStar_Range.range ->
    FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun t  ->
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1086 =
            let uu____1087 =
              let uu____1088 =
                let uu____1089 = embed_fvar rng fv in
                FStar_Syntax_Syntax.as_arg uu____1089 in
              [uu____1088] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
              uu____1087 in
          uu____1086 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1093 =
            let uu____1094 =
              let uu____1095 =
                let uu____1096 = embed_binder rng bv in
                FStar_Syntax_Syntax.as_arg uu____1096 in
              [uu____1095] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
              uu____1094 in
          uu____1093 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1101 =
            let uu____1102 =
              let uu____1103 =
                let uu____1104 = embed_term rng hd1 in
                FStar_Syntax_Syntax.as_arg uu____1104 in
              let uu____1105 =
                let uu____1108 =
                  let uu____1109 = embed_argv rng a in
                  FStar_Syntax_Syntax.as_arg uu____1109 in
                [uu____1108] in
              uu____1103 :: uu____1105 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
              uu____1102 in
          uu____1101 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1114 =
            let uu____1115 =
              let uu____1116 =
                let uu____1117 = embed_binder rng b in
                FStar_Syntax_Syntax.as_arg uu____1117 in
              let uu____1118 =
                let uu____1121 =
                  let uu____1122 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1122 in
                [uu____1121] in
              uu____1116 :: uu____1118 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
              uu____1115 in
          uu____1114 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1127 =
            let uu____1128 =
              let uu____1129 =
                let uu____1130 = embed_binder rng b in
                FStar_Syntax_Syntax.as_arg uu____1130 in
              let uu____1131 =
                let uu____1134 =
                  let uu____1135 = embed_comp rng c in
                  FStar_Syntax_Syntax.as_arg uu____1135 in
                [uu____1134] in
              uu____1129 :: uu____1131 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
              uu____1128 in
          uu____1127 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1139 =
            let uu____1140 =
              let uu____1141 =
                let uu____1142 = FStar_Syntax_Embeddings.embed_unit rng () in
                FStar_Syntax_Syntax.as_arg uu____1142 in
              [uu____1141] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
              uu____1140 in
          uu____1139 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1147 =
            let uu____1148 =
              let uu____1149 =
                let uu____1150 = embed_binder rng bv in
                FStar_Syntax_Syntax.as_arg uu____1150 in
              let uu____1151 =
                let uu____1154 =
                  let uu____1155 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1155 in
                [uu____1154] in
              uu____1149 :: uu____1151 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
              uu____1148 in
          uu____1147 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1159 =
            let uu____1160 =
              let uu____1161 =
                let uu____1162 = embed_const rng c in
                FStar_Syntax_Syntax.as_arg uu____1162 in
              [uu____1161] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
              uu____1160 in
          uu____1159 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____1167 =
            let uu____1168 =
              let uu____1169 =
                let uu____1170 = FStar_Syntax_Embeddings.embed_int rng u in
                FStar_Syntax_Syntax.as_arg uu____1170 in
              let uu____1171 =
                let uu____1174 =
                  let uu____1175 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1175 in
                [uu____1174] in
              uu____1169 :: uu____1171 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
              uu____1168 in
          uu____1167 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
          let uu____1181 =
            let uu____1182 =
              let uu____1183 =
                let uu____1184 = embed_binder rng b in
                FStar_Syntax_Syntax.as_arg uu____1184 in
              let uu____1185 =
                let uu____1188 =
                  let uu____1189 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1189 in
                let uu____1190 =
                  let uu____1193 =
                    let uu____1194 = embed_term rng t2 in
                    FStar_Syntax_Syntax.as_arg uu____1194 in
                  [uu____1193] in
                uu____1188 :: uu____1190 in
              uu____1183 :: uu____1185 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Let
              uu____1182 in
          uu____1181 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1203 =
            let uu____1204 =
              let uu____1205 =
                let uu____1206 = embed_term rng t1 in
                FStar_Syntax_Syntax.as_arg uu____1206 in
              let uu____1207 =
                let uu____1210 =
                  let uu____1211 =
                    let uu____1212 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch in
                    uu____1212 rng brs in
                  FStar_Syntax_Syntax.as_arg uu____1211 in
                [uu____1210] in
              uu____1205 :: uu____1207 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
              uu____1204 in
          uu____1203 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___124_1230 = FStar_Reflection_Data.ref_Tv_Unknown in
          {
            FStar_Syntax_Syntax.n = (uu___124_1230.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___124_1230.FStar_Syntax_Syntax.vars)
          }
let unembed_term_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1240 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1240 with
    | (hd1,args) ->
        let uu____1279 =
          let uu____1292 =
            let uu____1293 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1293.FStar_Syntax_Syntax.n in
          (uu____1292, args) in
        (match uu____1279 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1308)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1333 = unembed_binder b in
             FStar_Util.bind_opt uu____1333
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1342)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1367 = unembed_fvar f in
             FStar_Util.bind_opt uu____1367
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1376)::(r,uu____1378)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1413 = unembed_term l in
             FStar_Util.bind_opt uu____1413
               (fun l1  ->
                  let uu____1419 = unembed_argv r in
                  FStar_Util.bind_opt uu____1419
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1444)::(t2,uu____1446)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1481 = unembed_binder b in
             FStar_Util.bind_opt uu____1481
               (fun b1  ->
                  let uu____1487 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1487
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1496)::(t2,uu____1498)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1533 = unembed_binder b in
             FStar_Util.bind_opt uu____1533
               (fun b1  ->
                  let uu____1539 = unembed_comp t2 in
                  FStar_Util.bind_opt uu____1539
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1548)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             let uu____1573 = FStar_Syntax_Embeddings.unembed_unit u in
             FStar_Util.bind_opt uu____1573
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1582)::(t2,uu____1584)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1619 = unembed_binder b in
             FStar_Util.bind_opt uu____1619
               (fun b1  ->
                  let uu____1625 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1625
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1634)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1659 = unembed_const c in
             FStar_Util.bind_opt uu____1659
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1668)::(t2,uu____1670)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1705 = FStar_Syntax_Embeddings.unembed_int u in
             FStar_Util.bind_opt uu____1705
               (fun u1  ->
                  let uu____1711 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1711
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_55  -> FStar_Pervasives_Native.Some _0_55)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1720)::(t11,uu____1722)::(t2,uu____1724)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let_lid
             ->
             let uu____1769 = unembed_binder b in
             FStar_Util.bind_opt uu____1769
               (fun b1  ->
                  let uu____1775 = unembed_term t11 in
                  FStar_Util.bind_opt uu____1775
                    (fun t12  ->
                       let uu____1781 = unembed_term t2 in
                       FStar_Util.bind_opt uu____1781
                         (fun t21  ->
                            FStar_All.pipe_left
                              (fun _0_56  ->
                                 FStar_Pervasives_Native.Some _0_56)
                              (FStar_Reflection_Data.Tv_Let (b1, t12, t21)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1790)::(brs,uu____1792)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1827 = unembed_term t2 in
             FStar_Util.bind_opt uu____1827
               (fun t3  ->
                  let uu____1833 =
                    let uu____1842 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch in
                    uu____1842 brs in
                  FStar_Util.bind_opt uu____1833
                    (fun brs1  ->
                       FStar_All.pipe_left
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
                         (FStar_Reflection_Data.Tv_Match (t3, brs1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             ->
             FStar_All.pipe_left
               (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
               FStar_Reflection_Data.Tv_Unknown
         | uu____1896 ->
             ((let uu____1910 =
                 let uu____1911 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded term_view: %s"
                   uu____1911 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____1910);
              FStar_Pervasives_Native.None))
let embed_comp_view:
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total t ->
          let uu____1921 =
            let uu____1922 =
              let uu____1923 =
                let uu____1924 = embed_term rng t in
                FStar_Syntax_Syntax.as_arg uu____1924 in
              [uu____1923] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Total
              uu____1922 in
          uu____1921 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
          let uu____1932 =
            let uu____1933 =
              let uu____1934 =
                let uu____1935 = embed_term rng pre in
                FStar_Syntax_Syntax.as_arg uu____1935 in
              let uu____1936 =
                let uu____1939 =
                  let uu____1940 = embed_term rng post1 in
                  FStar_Syntax_Syntax.as_arg uu____1940 in
                [uu____1939] in
              uu____1934 :: uu____1936 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Lemma
              uu____1933 in
          uu____1932 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___125_1943 = FStar_Reflection_Data.ref_C_Unknown in
          {
            FStar_Syntax_Syntax.n = (uu___125_1943.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___125_1943.FStar_Syntax_Syntax.vars)
          }
let unembed_comp_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1953 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1953 with
    | (hd1,args) ->
        let uu____1992 =
          let uu____2005 =
            let uu____2006 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2006.FStar_Syntax_Syntax.n in
          (uu____2005, args) in
        (match uu____1992 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____2021)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total_lid
             ->
             let uu____2046 = unembed_term t2 in
             FStar_Util.bind_opt uu____2046
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_59  -> FStar_Pervasives_Native.Some _0_59)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2055)::(post,uu____2057)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma_lid
             ->
             let uu____2092 = unembed_term pre in
             FStar_Util.bind_opt uu____2092
               (fun pre1  ->
                  let uu____2098 = unembed_term post in
                  FStar_Util.bind_opt uu____2098
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_60  -> FStar_Pervasives_Native.Some _0_60)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown_lid
             ->
             FStar_All.pipe_left
               (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
               FStar_Reflection_Data.C_Unknown
         | uu____2122 ->
             ((let uu____2136 =
                 let uu____2137 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded comp_view: %s"
                   uu____2137 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____2136);
              FStar_Pervasives_Native.None))
let rec last: 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____2152::xs -> last xs
let rec init: 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____2178 = init xs in x :: uu____2178
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____2189 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____2189
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____2198 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____2198
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____2208) ->
        let uu____2221 = FStar_Util.int_of_string s in
        FStar_Reflection_Data.C_Int uu____2221
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____2223) ->
        FStar_Reflection_Data.C_String s
    | uu____2224 ->
        let uu____2225 =
          let uu____2226 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____2226 in
        failwith uu____2225
let rec inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let t2 = FStar_Syntax_Util.un_uinst t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____2234) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2240 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____2240
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2283 = last args in
        (match uu____2283 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____2303) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit in
             let uu____2304 =
               let uu____2309 =
                 let uu____2312 =
                   let uu____2313 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2313 in
                 uu____2312 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos in
               (uu____2309, (a, q')) in
             FStar_Reflection_Data.Tv_App uu____2304)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2332,uu____2333) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____2375 = FStar_Syntax_Subst.open_term bs t3 in
        (match uu____2375 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2402 =
                    let uu____2407 = FStar_Syntax_Util.abs bs2 t4 k in
                    (b, uu____2407) in
                  FStar_Reflection_Data.Tv_Abs uu____2402))
    | FStar_Syntax_Syntax.Tm_type uu____2412 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____2428 ->
        let uu____2441 = FStar_Syntax_Util.arrow_one t2 in
        (match uu____2441 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____2465 = FStar_Syntax_Subst.open_term [b] t3 in
        (match uu____2465 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2494 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2504 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____2504
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____2531 =
          let uu____2536 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____2536, t3) in
        FStar_Reflection_Data.Tv_Uvar uu____2531
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2556 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____2559 = FStar_Syntax_Subst.open_term [b] t21 in
               (match uu____2559 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____2588 ->
                          failwith
                            "impossible: open_term returned different amount of binders" in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2646 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____2646
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2665 =
                let uu____2672 =
                  FStar_List.map
                    (fun uu____2684  ->
                       match uu____2684 with
                       | (p1,uu____2692) -> inspect_pat p1) ps in
                (fv, uu____2672) in
              FStar_Reflection_Data.Pat_Cons uu____2665
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2701 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___111_2745  ->
               match uu___111_2745 with
               | (pat,uu____2767,t4) ->
                   let uu____2785 = inspect_pat pat in (uu____2785, t4)) brs1 in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2798 ->
        ((let uu____2800 = FStar_Syntax_Print.tag_of_term t2 in
          let uu____2801 = FStar_Syntax_Print.term_to_string t2 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____2800 uu____2801);
         FStar_Reflection_Data.Tv_Unknown)
let inspect_comp: FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2807) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2818)::(post,uu____2820)::uu____2821 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2854 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____2864 ->
        FStar_Reflection_Data.C_Unknown
let pack_comp: FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____2878 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2884 =
          let uu____2895 = FStar_Util.string_of_int i in
          (uu____2895, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____2884
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2912) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2921 =
               let uu____2930 = FStar_Syntax_Syntax.as_arg r in [uu____2930] in
             FStar_Syntax_Util.mk_app l uu____2921
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2931 =
               let uu____2940 = FStar_Syntax_Syntax.iarg r in [uu____2940] in
             FStar_Syntax_Util.mk_app l uu____2931)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2946),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2953 =
          let uu____2956 =
            let uu____2957 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____2957 in
          FStar_Syntax_Syntax.mk uu____2956 in
        uu____2953 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        FStar_Syntax_Util.uvar_from_id u t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 in
        let uu____2968 =
          let uu____2971 =
            let uu____2972 =
              let uu____2985 = FStar_Syntax_Subst.close [b] t2 in
              ((false, [lb]), uu____2985) in
            FStar_Syntax_Syntax.Tm_let uu____2972 in
          FStar_Syntax_Syntax.mk uu____2971 in
        uu____2968 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____3014 =
                let uu____3015 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____3015 in
              FStar_All.pipe_left wrap uu____3014
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____3024 =
                let uu____3025 =
                  let uu____3038 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____3052 = pack_pat p1 in (uu____3052, false))
                      ps in
                  (fv, uu____3038) in
                FStar_Syntax_Syntax.Pat_cons uu____3025 in
              FStar_All.pipe_left wrap uu____3024
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___112_3098  ->
               match uu___112_3098 with
               | (pat,t1) ->
                   let uu____3115 = pack_pat pat in
                   (uu____3115, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        failwith "pack: unexpected term view"
let embed_order:
  FStar_Range.range -> FStar_Order.order -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun o  ->
      let r =
        match o with
        | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
        | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
        | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt in
      let uu___126_3136 = r in
      {
        FStar_Syntax_Syntax.n = (uu___126_3136.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___126_3136.FStar_Syntax_Syntax.vars)
      }
let unembed_order:
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3146 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3146 with
    | (hd1,args) ->
        let uu____3185 =
          let uu____3198 =
            let uu____3199 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3199.FStar_Syntax_Syntax.n in
          (uu____3198, args) in
        (match uu____3185 with
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
         | uu____3257 ->
             ((let uu____3271 =
                 let uu____3272 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded order: %s" uu____3272 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____3271);
              FStar_Pervasives_Native.None))
let compare_binder:
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder -> FStar_Order.order
  =
  fun x  ->
    fun y  ->
      let n1 =
        FStar_Syntax_Syntax.order_bv (FStar_Pervasives_Native.fst x)
          (FStar_Pervasives_Native.fst y) in
      if n1 < (Prims.parse_int "0")
      then FStar_Order.Lt
      else
        if n1 = (Prims.parse_int "0") then FStar_Order.Eq else FStar_Order.Gt
let is_free:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    fun t  -> FStar_Syntax_Util.is_free_in (FStar_Pervasives_Native.fst x) t
let lookup_typ:
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list -> FStar_Reflection_Data.sigelt_view
  =
  fun env  ->
    fun ns  ->
      let lid = FStar_Parser_Const.p2l ns in
      let res = FStar_TypeChecker_Env.lookup_qname env lid in
      match res with
      | FStar_Pervasives_Native.None  -> FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____3344,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____3445,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____3462 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____3462 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____3535,n1,uu____3537) ->
                          let uu____3542 =
                            let uu____3547 = FStar_Ident.path_of_lid lid2 in
                            (uu____3547, t1) in
                          FStar_Reflection_Data.Ctor uu____3542
                      | uu____3552 -> failwith "wat 1")
                 | uu____3553 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3582) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____3597 ->
                     failwith "global Sig_let has bv" in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____3602 -> FStar_Reflection_Data.Unk)
let embed_ctor:
  FStar_Range.range -> FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun c  ->
      match c with
      | FStar_Reflection_Data.Ctor (nm,t) ->
          let uu____3613 =
            let uu____3614 =
              let uu____3615 =
                let uu____3616 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm in
                FStar_Syntax_Syntax.as_arg uu____3616 in
              let uu____3617 =
                let uu____3620 =
                  let uu____3621 = embed_term rng t in
                  FStar_Syntax_Syntax.as_arg uu____3621 in
                [uu____3620] in
              uu____3615 :: uu____3617 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
              uu____3614 in
          uu____3613 FStar_Pervasives_Native.None rng
let unembed_ctor:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.ctor FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3633 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3633 with
    | (hd1,args) ->
        let uu____3672 =
          let uu____3685 =
            let uu____3686 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3686.FStar_Syntax_Syntax.n in
          (uu____3685, args) in
        (match uu____3672 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3701)::(t2,uu____3703)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____3738 = FStar_Syntax_Embeddings.unembed_string_list nm in
             FStar_Util.bind_opt uu____3738
               (fun nm1  ->
                  let uu____3750 = unembed_term t2 in
                  FStar_Util.bind_opt uu____3750
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_62  -> FStar_Pervasives_Native.Some _0_62)
                         (FStar_Reflection_Data.Ctor (nm1, t3))))
         | uu____3759 ->
             ((let uu____3773 =
                 let uu____3774 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded ctor: %s" uu____3774 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____3773);
              FStar_Pervasives_Native.None))
let embed_sigelt_view:
  FStar_Range.range ->
    FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun sev  ->
      match sev with
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____3795 =
            let uu____3796 =
              let uu____3797 =
                let uu____3798 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm in
                FStar_Syntax_Syntax.as_arg uu____3798 in
              let uu____3799 =
                let uu____3802 =
                  let uu____3803 = embed_binders rng bs in
                  FStar_Syntax_Syntax.as_arg uu____3803 in
                let uu____3804 =
                  let uu____3807 =
                    let uu____3808 = embed_term rng t in
                    FStar_Syntax_Syntax.as_arg uu____3808 in
                  let uu____3809 =
                    let uu____3812 =
                      let uu____3813 =
                        let uu____3814 =
                          FStar_Syntax_Embeddings.embed_list embed_ctor
                            FStar_Reflection_Data.fstar_refl_ctor in
                        uu____3814 rng dcs in
                      FStar_Syntax_Syntax.as_arg uu____3813 in
                    [uu____3812] in
                  uu____3807 :: uu____3809 in
                uu____3802 :: uu____3804 in
              uu____3797 :: uu____3799 in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive uu____3796 in
          uu____3795 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
          let uu____3827 =
            let uu____3828 =
              let uu____3829 =
                let uu____3830 = embed_fvar rng fv in
                FStar_Syntax_Syntax.as_arg uu____3830 in
              let uu____3831 =
                let uu____3834 =
                  let uu____3835 = embed_term rng ty in
                  FStar_Syntax_Syntax.as_arg uu____3835 in
                let uu____3836 =
                  let uu____3839 =
                    let uu____3840 = embed_term rng t in
                    FStar_Syntax_Syntax.as_arg uu____3840 in
                  [uu____3839] in
                uu____3834 :: uu____3836 in
              uu____3829 :: uu____3831 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Let
              uu____3828 in
          uu____3827 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___127_3843 = FStar_Reflection_Data.ref_Unk in
          {
            FStar_Syntax_Syntax.n = (uu___127_3843.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___127_3843.FStar_Syntax_Syntax.vars)
          }
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3853 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3853 with
    | (hd1,args) ->
        let uu____3892 =
          let uu____3905 =
            let uu____3906 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3906.FStar_Syntax_Syntax.n in
          (uu____3905, args) in
        (match uu____3892 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3921)::(bs,uu____3923)::(t2,uu____3925)::(dcs,uu____3927)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3982 = FStar_Syntax_Embeddings.unembed_string_list nm in
             FStar_Util.bind_opt uu____3982
               (fun nm1  ->
                  let uu____3994 = unembed_binders bs in
                  FStar_Util.bind_opt uu____3994
                    (fun bs1  ->
                       let uu____4006 = unembed_term t2 in
                       FStar_Util.bind_opt uu____4006
                         (fun t3  ->
                            let uu____4012 =
                              let uu____4017 =
                                FStar_Syntax_Embeddings.unembed_list
                                  unembed_ctor in
                              uu____4017 dcs in
                            FStar_Util.bind_opt uu____4012
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_Pervasives_Native.Some _0_63)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____4040)::(ty,uu____4042)::(t2,uu____4044)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let_lid
             ->
             let uu____4089 = unembed_fvar fvar1 in
             FStar_Util.bind_opt uu____4089
               (fun fvar2  ->
                  let uu____4095 = unembed_term ty in
                  FStar_Util.bind_opt uu____4095
                    (fun ty1  ->
                       let uu____4101 = unembed_term t2 in
                       FStar_Util.bind_opt uu____4101
                         (fun t3  ->
                            FStar_All.pipe_left
                              (fun _0_64  ->
                                 FStar_Pervasives_Native.Some _0_64)
                              (FStar_Reflection_Data.Sg_Let (fvar2, ty1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____4123 ->
             ((let uu____4137 =
                 let uu____4138 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded sigelt_view: %s"
                   uu____4138 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____4137);
              FStar_Pervasives_Native.None))
let binders_of_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders
  = fun e  -> FStar_TypeChecker_Env.all_binders e
let type_of_binder:
  'Auu____4147 .
    (FStar_Syntax_Syntax.bv,'Auu____4147) FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun b  -> match b with | (b1,uu____4163) -> b1.FStar_Syntax_Syntax.sort
let term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  FStar_Syntax_Util.term_eq
let fresh_binder:
  'Auu____4174 .
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.bv,'Auu____4174 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____4185 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t in
    (uu____4185, FStar_Pervasives_Native.None)
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  FStar_Syntax_Print.term_to_string