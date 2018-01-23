open Prims
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____4 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None in
    FStar_All.pipe_right uu____4 FStar_Syntax_Syntax.fv_to_tm
let fstar_refl_embed: FStar_Syntax_Syntax.term =
  lid_as_tm FStar_Parser_Const.fstar_refl_embed_lid
let protect_embedded_term:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      let uu____13 =
        let uu____14 =
          let uu____15 = FStar_Syntax_Syntax.iarg t in
          let uu____16 =
            let uu____19 = FStar_Syntax_Syntax.as_arg x in [uu____19] in
          uu____15 :: uu____16 in
        FStar_Syntax_Syntax.mk_Tm_app fstar_refl_embed uu____14 in
      uu____13 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos
let un_protect_embedded_term:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____29 =
      let uu____44 = FStar_Syntax_Util.unmeta t in
      FStar_Syntax_Util.head_and_args uu____44 in
    match uu____29 with
    | (head1,args) ->
        let uu____69 =
          let uu____82 =
            let uu____83 = FStar_Syntax_Util.un_uinst head1 in
            uu____83.FStar_Syntax_Syntax.n in
          (uu____82, args) in
        (match uu____69 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____97::(x,uu____99)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_refl_embed_lid
             -> FStar_Pervasives_Native.Some x
         | uu____138 ->
             ((let uu____152 =
                 let uu____157 =
                   let uu____158 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.format1 "Not an protected term: %s" uu____158 in
                 (FStar_Errors.Warning_UnprotectedTerm, uu____157) in
               FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____152);
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
      let uu____179 =
        let uu____180 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____180 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____179
    with
    | uu____187 ->
        ((let uu____189 =
            let uu____194 =
              let uu____195 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded binder: %s" uu____195 in
            (FStar_Errors.Warning_NotEmbedded, uu____194) in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____189);
         FStar_Pervasives_Native.None)
let embed_binders:
  FStar_Range.range ->
    FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun l  ->
      let uu____206 =
        FStar_Syntax_Embeddings.embed_list embed_binder
          FStar_Reflection_Data.fstar_refl_binder in
      uu____206 rng l
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
      let uu___56_237 = t1 in
      {
        FStar_Syntax_Syntax.n = (uu___56_237.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___56_237.FStar_Syntax_Syntax.vars)
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
      let uu____267 =
        let uu____268 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____268 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____267
    with
    | uu____275 ->
        ((let uu____277 =
            let uu____282 =
              let uu____283 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____283 in
            (FStar_Errors.Warning_NotEmbedded, uu____282) in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____277);
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
      let uu____304 =
        let uu____305 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____305 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____304
    with
    | uu____312 ->
        ((let uu____314 =
            let uu____319 =
              let uu____320 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded comp: %s" uu____320 in
            (FStar_Errors.Warning_NotEmbedded, uu____319) in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____314);
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
      let uu____341 =
        let uu____342 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____342 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____341
    with
    | uu____349 ->
        ((let uu____351 =
            let uu____356 =
              let uu____357 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded env: %s" uu____357 in
            (FStar_Errors.Warning_NotEmbedded, uu____356) in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____351);
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
            let uu____366 =
              let uu____367 =
                let uu____368 =
                  let uu____369 =
                    let uu____370 = FStar_BigInt.string_of_big_int i in
                    FStar_Syntax_Util.exp_int uu____370 in
                  FStar_Syntax_Syntax.as_arg uu____369 in
                [uu____368] in
              FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
                uu____367 in
            uu____366 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____374 =
              let uu____375 =
                let uu____376 =
                  let uu____377 = FStar_Syntax_Embeddings.embed_string rng s in
                  FStar_Syntax_Syntax.as_arg uu____377 in
                [uu____376] in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String uu____375 in
            uu____374 FStar_Pervasives_Native.None FStar_Range.dummyRange in
      let uu___63_380 = r in
      {
        FStar_Syntax_Syntax.n = (uu___63_380.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___63_380.FStar_Syntax_Syntax.vars)
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
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____536)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____561 = FStar_Syntax_Embeddings.unembed_string s in
             FStar_Util.bind_opt uu____561
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____568 ->
             ((let uu____582 =
                 let uu____587 =
                   let uu____588 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____588 in
                 (FStar_Errors.Warning_NotEmbedded, uu____587) in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____582);
              FStar_Pervasives_Native.None))
let rec embed_pattern:
  FStar_Range.range ->
    FStar_Reflection_Data.pattern -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____596 =
            let uu____597 =
              let uu____598 =
                let uu____599 = embed_const rng c in
                FStar_Syntax_Syntax.as_arg uu____599 in
              [uu____598] in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant uu____597 in
          uu____596 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____608 =
            let uu____609 =
              let uu____610 =
                let uu____611 = embed_fvar rng fv in
                FStar_Syntax_Syntax.as_arg uu____611 in
              let uu____612 =
                let uu____615 =
                  let uu____616 =
                    let uu____617 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern in
                    uu____617 rng ps in
                  FStar_Syntax_Syntax.as_arg uu____616 in
                [uu____615] in
              uu____610 :: uu____612 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
              uu____609 in
          uu____608 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____628 =
            let uu____629 =
              let uu____630 =
                let uu____631 =
                  let uu____632 = FStar_Syntax_Syntax.mk_binder bv in
                  embed_binder rng uu____632 in
                FStar_Syntax_Syntax.as_arg uu____631 in
              [uu____630] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
              uu____629 in
          uu____628 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____636 =
            let uu____637 =
              let uu____638 =
                let uu____639 =
                  let uu____640 = FStar_Syntax_Syntax.mk_binder bv in
                  embed_binder rng uu____640 in
                FStar_Syntax_Syntax.as_arg uu____639 in
              [uu____638] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
              uu____637 in
          uu____636 FStar_Pervasives_Native.None rng
let rec unembed_pattern:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.pattern FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____651 = FStar_Syntax_Util.head_and_args t1 in
    match uu____651 with
    | (hd1,args) ->
        let uu____690 =
          let uu____703 =
            let uu____704 = FStar_Syntax_Util.un_uinst hd1 in
            uu____704.FStar_Syntax_Syntax.n in
          (uu____703, args) in
        (match uu____690 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____719)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____744 = unembed_const c in
             FStar_Util.bind_opt uu____744
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____753)::(ps,uu____755)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____790 = unembed_fvar f in
             FStar_Util.bind_opt uu____790
               (fun f1  ->
                  let uu____796 =
                    let uu____801 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern in
                    uu____801 ps in
                  FStar_Util.bind_opt uu____796
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____820)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____845 = unembed_binder b in
             FStar_Util.bind_opt uu____845
               (fun uu____851  ->
                  match uu____851 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                        (FStar_Reflection_Data.Pat_Var bv))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____860)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____885 = unembed_binder b in
             FStar_Util.bind_opt uu____885
               (fun uu____891  ->
                  match uu____891 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                        (FStar_Reflection_Data.Pat_Wild bv))
         | uu____898 ->
             ((let uu____912 =
                 let uu____917 =
                   let uu____918 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.format1 "Not an embedded pattern: %s" uu____918 in
                 (FStar_Errors.Warning_NotEmbedded, uu____917) in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____912);
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
      let uu___64_943 = r in
      {
        FStar_Syntax_Syntax.n = (uu___64_943.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___64_943.FStar_Syntax_Syntax.vars)
      }
let unembed_aqualv:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____952 = FStar_Syntax_Util.head_and_args t1 in
    match uu____952 with
    | (hd1,args) ->
        let uu____991 =
          let uu____1004 =
            let uu____1005 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1005.FStar_Syntax_Syntax.n in
          (uu____1004, args) in
        (match uu____991 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____1048 ->
             ((let uu____1062 =
                 let uu____1067 =
                   let uu____1068 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____1068 in
                 (FStar_Errors.Warning_NotEmbedded, uu____1067) in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1062);
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
          let uu____1093 =
            let uu____1094 =
              let uu____1095 =
                let uu____1096 = embed_fvar rng fv in
                FStar_Syntax_Syntax.as_arg uu____1096 in
              [uu____1095] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
              uu____1094 in
          uu____1093 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1100 =
            let uu____1101 =
              let uu____1102 =
                let uu____1103 = embed_binder rng bv in
                FStar_Syntax_Syntax.as_arg uu____1103 in
              [uu____1102] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
              uu____1101 in
          uu____1100 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1108 =
            let uu____1109 =
              let uu____1110 =
                let uu____1111 = embed_term rng hd1 in
                FStar_Syntax_Syntax.as_arg uu____1111 in
              let uu____1112 =
                let uu____1115 =
                  let uu____1116 = embed_argv rng a in
                  FStar_Syntax_Syntax.as_arg uu____1116 in
                [uu____1115] in
              uu____1110 :: uu____1112 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
              uu____1109 in
          uu____1108 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1121 =
            let uu____1122 =
              let uu____1123 =
                let uu____1124 = embed_binder rng b in
                FStar_Syntax_Syntax.as_arg uu____1124 in
              let uu____1125 =
                let uu____1128 =
                  let uu____1129 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1129 in
                [uu____1128] in
              uu____1123 :: uu____1125 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
              uu____1122 in
          uu____1121 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1134 =
            let uu____1135 =
              let uu____1136 =
                let uu____1137 = embed_binder rng b in
                FStar_Syntax_Syntax.as_arg uu____1137 in
              let uu____1138 =
                let uu____1141 =
                  let uu____1142 = embed_comp rng c in
                  FStar_Syntax_Syntax.as_arg uu____1142 in
                [uu____1141] in
              uu____1136 :: uu____1138 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
              uu____1135 in
          uu____1134 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1146 =
            let uu____1147 =
              let uu____1148 =
                let uu____1149 = FStar_Syntax_Embeddings.embed_unit rng () in
                FStar_Syntax_Syntax.as_arg uu____1149 in
              [uu____1148] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
              uu____1147 in
          uu____1146 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1154 =
            let uu____1155 =
              let uu____1156 =
                let uu____1157 = embed_binder rng bv in
                FStar_Syntax_Syntax.as_arg uu____1157 in
              let uu____1158 =
                let uu____1161 =
                  let uu____1162 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1162 in
                [uu____1161] in
              uu____1156 :: uu____1158 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
              uu____1155 in
          uu____1154 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1166 =
            let uu____1167 =
              let uu____1168 =
                let uu____1169 = embed_const rng c in
                FStar_Syntax_Syntax.as_arg uu____1169 in
              [uu____1168] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
              uu____1167 in
          uu____1166 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____1174 =
            let uu____1175 =
              let uu____1176 =
                let uu____1177 = FStar_Syntax_Embeddings.embed_int rng u in
                FStar_Syntax_Syntax.as_arg uu____1177 in
              let uu____1178 =
                let uu____1181 =
                  let uu____1182 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1182 in
                [uu____1181] in
              uu____1176 :: uu____1178 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
              uu____1175 in
          uu____1174 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
          let uu____1188 =
            let uu____1189 =
              let uu____1190 =
                let uu____1191 = embed_binder rng b in
                FStar_Syntax_Syntax.as_arg uu____1191 in
              let uu____1192 =
                let uu____1195 =
                  let uu____1196 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1196 in
                let uu____1197 =
                  let uu____1200 =
                    let uu____1201 = embed_term rng t2 in
                    FStar_Syntax_Syntax.as_arg uu____1201 in
                  [uu____1200] in
                uu____1195 :: uu____1197 in
              uu____1190 :: uu____1192 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Let
              uu____1189 in
          uu____1188 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1210 =
            let uu____1211 =
              let uu____1212 =
                let uu____1213 = embed_term rng t1 in
                FStar_Syntax_Syntax.as_arg uu____1213 in
              let uu____1214 =
                let uu____1217 =
                  let uu____1218 =
                    let uu____1219 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch in
                    uu____1219 rng brs in
                  FStar_Syntax_Syntax.as_arg uu____1218 in
                [uu____1217] in
              uu____1212 :: uu____1214 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
              uu____1211 in
          uu____1210 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___65_1237 = FStar_Reflection_Data.ref_Tv_Unknown in
          {
            FStar_Syntax_Syntax.n = (uu___65_1237.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___65_1237.FStar_Syntax_Syntax.vars)
          }
let unembed_term_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1246 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1246 with
    | (hd1,args) ->
        let uu____1285 =
          let uu____1298 =
            let uu____1299 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1299.FStar_Syntax_Syntax.n in
          (uu____1298, args) in
        (match uu____1285 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1314)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1339 = unembed_binder b in
             FStar_Util.bind_opt uu____1339
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1348)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1373 = unembed_fvar f in
             FStar_Util.bind_opt uu____1373
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1382)::(r,uu____1384)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1419 = unembed_term l in
             FStar_Util.bind_opt uu____1419
               (fun l1  ->
                  let uu____1425 = unembed_argv r in
                  FStar_Util.bind_opt uu____1425
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1450)::(t2,uu____1452)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1487 = unembed_binder b in
             FStar_Util.bind_opt uu____1487
               (fun b1  ->
                  let uu____1493 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1493
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1502)::(t2,uu____1504)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1539 = unembed_binder b in
             FStar_Util.bind_opt uu____1539
               (fun b1  ->
                  let uu____1545 = unembed_comp t2 in
                  FStar_Util.bind_opt uu____1545
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1554)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             let uu____1579 = FStar_Syntax_Embeddings.unembed_unit u in
             FStar_Util.bind_opt uu____1579
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1588)::(t2,uu____1590)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1625 = unembed_binder b in
             FStar_Util.bind_opt uu____1625
               (fun b1  ->
                  let uu____1631 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1631
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1640)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1665 = unembed_const c in
             FStar_Util.bind_opt uu____1665
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1674)::(t2,uu____1676)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1711 = FStar_Syntax_Embeddings.unembed_int u in
             FStar_Util.bind_opt uu____1711
               (fun u1  ->
                  let uu____1717 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1717
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1726)::(t11,uu____1728)::(t2,uu____1730)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let_lid
             ->
             let uu____1775 = unembed_binder b in
             FStar_Util.bind_opt uu____1775
               (fun b1  ->
                  let uu____1781 = unembed_term t11 in
                  FStar_Util.bind_opt uu____1781
                    (fun t12  ->
                       let uu____1787 = unembed_term t2 in
                       FStar_Util.bind_opt uu____1787
                         (fun t21  ->
                            FStar_All.pipe_left
                              (fun _0_55  ->
                                 FStar_Pervasives_Native.Some _0_55)
                              (FStar_Reflection_Data.Tv_Let (b1, t12, t21)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1796)::(brs,uu____1798)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1833 = unembed_term t2 in
             FStar_Util.bind_opt uu____1833
               (fun t3  ->
                  let uu____1839 =
                    let uu____1848 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch in
                    uu____1848 brs in
                  FStar_Util.bind_opt uu____1839
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
         | uu____1902 ->
             ((let uu____1916 =
                 let uu____1921 =
                   let uu____1922 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____1922 in
                 (FStar_Errors.Warning_NotEmbedded, uu____1921) in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1916);
              FStar_Pervasives_Native.None))
let embed_comp_view:
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total t ->
          let uu____1930 =
            let uu____1931 =
              let uu____1932 =
                let uu____1933 = embed_term rng t in
                FStar_Syntax_Syntax.as_arg uu____1933 in
              [uu____1932] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Total
              uu____1931 in
          uu____1930 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
          let uu____1941 =
            let uu____1942 =
              let uu____1943 =
                let uu____1944 = embed_term rng pre in
                FStar_Syntax_Syntax.as_arg uu____1944 in
              let uu____1945 =
                let uu____1948 =
                  let uu____1949 = embed_term rng post1 in
                  FStar_Syntax_Syntax.as_arg uu____1949 in
                [uu____1948] in
              uu____1943 :: uu____1945 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Lemma
              uu____1942 in
          uu____1941 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___66_1952 = FStar_Reflection_Data.ref_C_Unknown in
          {
            FStar_Syntax_Syntax.n = (uu___66_1952.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___66_1952.FStar_Syntax_Syntax.vars)
          }
let unembed_comp_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1961 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1961 with
    | (hd1,args) ->
        let uu____2000 =
          let uu____2013 =
            let uu____2014 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2014.FStar_Syntax_Syntax.n in
          (uu____2013, args) in
        (match uu____2000 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____2029)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total_lid
             ->
             let uu____2054 = unembed_term t2 in
             FStar_Util.bind_opt uu____2054
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2063)::(post,uu____2065)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma_lid
             ->
             let uu____2100 = unembed_term pre in
             FStar_Util.bind_opt uu____2100
               (fun pre1  ->
                  let uu____2106 = unembed_term post in
                  FStar_Util.bind_opt uu____2106
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
         | uu____2130 ->
             ((let uu____2144 =
                 let uu____2149 =
                   let uu____2150 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2150 in
                 (FStar_Errors.Warning_NotEmbedded, uu____2149) in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2144);
              FStar_Pervasives_Native.None))
let rec last: 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____2164::xs -> last xs
let rec init: 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____2189 = init xs in x :: uu____2189
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____2199 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____2199
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____2207 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____2207
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____2215) ->
        let uu____2228 = FStar_BigInt.big_int_of_string s in
        FStar_Reflection_Data.C_Int uu____2228
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____2230) ->
        FStar_Reflection_Data.C_String s
    | uu____2231 ->
        let uu____2232 =
          let uu____2233 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____2233 in
        failwith uu____2232
let rec inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let t2 = FStar_Syntax_Util.un_uinst t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____2240) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2246 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____2246
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2289 = last args in
        (match uu____2289 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____2309) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit in
             let uu____2310 =
               let uu____2315 =
                 let uu____2318 =
                   let uu____2319 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2319 in
                 uu____2318 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos in
               (uu____2315, (a, q')) in
             FStar_Reflection_Data.Tv_App uu____2310)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2338,uu____2339) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____2381 = FStar_Syntax_Subst.open_term bs t3 in
        (match uu____2381 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2408 =
                    let uu____2413 = FStar_Syntax_Util.abs bs2 t4 k in
                    (b, uu____2413) in
                  FStar_Reflection_Data.Tv_Abs uu____2408))
    | FStar_Syntax_Syntax.Tm_type uu____2418 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____2434 ->
        let uu____2447 = FStar_Syntax_Util.arrow_one t2 in
        (match uu____2447 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____2471 = FStar_Syntax_Subst.open_term [b] t3 in
        (match uu____2471 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2500 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2510 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____2510
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____2537 =
          let uu____2542 =
            let uu____2543 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_BigInt.of_int_fs uu____2543 in
          (uu____2542, t3) in
        FStar_Reflection_Data.Tv_Uvar uu____2537
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2563 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____2566 = FStar_Syntax_Subst.open_term [b] t21 in
               (match uu____2566 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____2595 ->
                          failwith
                            "impossible: open_term returned different amount of binders" in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2653 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____2653
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2672 =
                let uu____2679 =
                  FStar_List.map
                    (fun uu____2691  ->
                       match uu____2691 with
                       | (p1,uu____2699) -> inspect_pat p1) ps in
                (fv, uu____2679) in
              FStar_Reflection_Data.Pat_Cons uu____2672
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2708 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___52_2752  ->
               match uu___52_2752 with
               | (pat,uu____2774,t4) ->
                   let uu____2792 = inspect_pat pat in (uu____2792, t4)) brs1 in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2805 ->
        ((let uu____2807 = FStar_Syntax_Print.tag_of_term t2 in
          let uu____2808 = FStar_Syntax_Print.term_to_string t2 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____2807 uu____2808);
         FStar_Reflection_Data.Tv_Unknown)
let inspect_comp: FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2813) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2824)::(post,uu____2826)::uu____2827 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2860 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____2870 ->
        FStar_Reflection_Data.C_Unknown
let pack_comp: FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____2883 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2888 =
          let uu____2899 = FStar_BigInt.string_of_big_int i in
          (uu____2899, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____2888
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2915) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2924 =
               let uu____2933 = FStar_Syntax_Syntax.as_arg r in [uu____2933] in
             FStar_Syntax_Util.mk_app l uu____2924
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2934 =
               let uu____2943 = FStar_Syntax_Syntax.iarg r in [uu____2943] in
             FStar_Syntax_Util.mk_app l uu____2934)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2949),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2956 =
          let uu____2959 =
            let uu____2960 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____2960 in
          FStar_Syntax_Syntax.mk uu____2959 in
        uu____2956 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____2966 = FStar_BigInt.to_int_fs u in
        FStar_Syntax_Util.uvar_from_id uu____2966 t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 in
        let uu____2972 =
          let uu____2975 =
            let uu____2976 =
              let uu____2989 = FStar_Syntax_Subst.close [b] t2 in
              ((false, [lb]), uu____2989) in
            FStar_Syntax_Syntax.Tm_let uu____2976 in
          FStar_Syntax_Syntax.mk uu____2975 in
        uu____2972 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____3018 =
                let uu____3019 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____3019 in
              FStar_All.pipe_left wrap uu____3018
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____3028 =
                let uu____3029 =
                  let uu____3042 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____3056 = pack_pat p1 in (uu____3056, false))
                      ps in
                  (fv, uu____3042) in
                FStar_Syntax_Syntax.Pat_cons uu____3029 in
              FStar_All.pipe_left wrap uu____3028
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___53_3102  ->
               match uu___53_3102 with
               | (pat,t1) ->
                   let uu____3119 = pack_pat pat in
                   (uu____3119, FStar_Pervasives_Native.None, t1)) brs in
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
      let uu___67_3138 = r in
      {
        FStar_Syntax_Syntax.n = (uu___67_3138.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___67_3138.FStar_Syntax_Syntax.vars)
      }
let unembed_order:
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3147 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3147 with
    | (hd1,args) ->
        let uu____3186 =
          let uu____3199 =
            let uu____3200 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3200.FStar_Syntax_Syntax.n in
          (uu____3199, args) in
        (match uu____3186 with
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
         | uu____3258 ->
             ((let uu____3272 =
                 let uu____3277 =
                   let uu____3278 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.format1 "Not an embedded order: %s" uu____3278 in
                 (FStar_Errors.Warning_NotEmbedded, uu____3277) in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3272);
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
          let uu____3611 =
            let uu____3612 =
              let uu____3613 =
                let uu____3614 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm in
                FStar_Syntax_Syntax.as_arg uu____3614 in
              let uu____3615 =
                let uu____3618 =
                  let uu____3619 = embed_term rng t in
                  FStar_Syntax_Syntax.as_arg uu____3619 in
                [uu____3618] in
              uu____3613 :: uu____3615 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
              uu____3612 in
          uu____3611 FStar_Pervasives_Native.None rng
let unembed_ctor:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.ctor FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3630 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3630 with
    | (hd1,args) ->
        let uu____3669 =
          let uu____3682 =
            let uu____3683 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3683.FStar_Syntax_Syntax.n in
          (uu____3682, args) in
        (match uu____3669 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3698)::(t2,uu____3700)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____3735 = FStar_Syntax_Embeddings.unembed_string_list nm in
             FStar_Util.bind_opt uu____3735
               (fun nm1  ->
                  let uu____3747 = unembed_term t2 in
                  FStar_Util.bind_opt uu____3747
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                         (FStar_Reflection_Data.Ctor (nm1, t3))))
         | uu____3756 ->
             ((let uu____3770 =
                 let uu____3775 =
                   let uu____3776 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.format1 "Not an embedded ctor: %s" uu____3776 in
                 (FStar_Errors.Warning_NotEmbedded, uu____3775) in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3770);
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
          let uu___68_3843 = FStar_Reflection_Data.ref_Unk in
          {
            FStar_Syntax_Syntax.n = (uu___68_3843.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___68_3843.FStar_Syntax_Syntax.vars)
          }
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3852 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3852 with
    | (hd1,args) ->
        let uu____3891 =
          let uu____3904 =
            let uu____3905 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3905.FStar_Syntax_Syntax.n in
          (uu____3904, args) in
        (match uu____3891 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3920)::(bs,uu____3922)::(t2,uu____3924)::(dcs,uu____3926)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3981 = FStar_Syntax_Embeddings.unembed_string_list nm in
             FStar_Util.bind_opt uu____3981
               (fun nm1  ->
                  let uu____3993 = unembed_binders bs in
                  FStar_Util.bind_opt uu____3993
                    (fun bs1  ->
                       let uu____4005 = unembed_term t2 in
                       FStar_Util.bind_opt uu____4005
                         (fun t3  ->
                            let uu____4011 =
                              let uu____4016 =
                                FStar_Syntax_Embeddings.unembed_list
                                  unembed_ctor in
                              uu____4016 dcs in
                            FStar_Util.bind_opt uu____4011
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____4039)::(ty,uu____4041)::(t2,uu____4043)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let_lid
             ->
             let uu____4088 = unembed_fvar fvar1 in
             FStar_Util.bind_opt uu____4088
               (fun fvar2  ->
                  let uu____4094 = unembed_term ty in
                  FStar_Util.bind_opt uu____4094
                    (fun ty1  ->
                       let uu____4100 = unembed_term t2 in
                       FStar_Util.bind_opt uu____4100
                         (fun t3  ->
                            FStar_All.pipe_left
                              (fun _0_63  ->
                                 FStar_Pervasives_Native.Some _0_63)
                              (FStar_Reflection_Data.Sg_Let (fvar2, ty1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____4122 ->
             ((let uu____4136 =
                 let uu____4141 =
                   let uu____4142 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____4142 in
                 (FStar_Errors.Warning_NotEmbedded, uu____4141) in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4136);
              FStar_Pervasives_Native.None))
let binders_of_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders
  = fun e  -> FStar_TypeChecker_Env.all_binders e
let type_of_binder:
  'Auu____4148 .
    (FStar_Syntax_Syntax.bv,'Auu____4148) FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun b  -> match b with | (b1,uu____4164) -> b1.FStar_Syntax_Syntax.sort
let term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  FStar_Syntax_Util.term_eq
let fresh_binder:
  'Auu____4171 .
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.bv,'Auu____4171 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____4182 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t in
    (uu____4182, FStar_Pervasives_Native.None)
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  FStar_Syntax_Print.term_to_string