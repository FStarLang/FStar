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
                 let uu____153 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format1 "Not an protected term: %s" uu____153 in
               FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____152);
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
      let uu____174 =
        let uu____175 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____175 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____174
    with
    | uu____182 ->
        ((let uu____184 =
            let uu____185 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded binder: %s" uu____185 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____184);
         FStar_Pervasives_Native.None)
let embed_binders:
  FStar_Range.range ->
    FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun l  ->
      let uu____196 =
        FStar_Syntax_Embeddings.embed_list embed_binder
          FStar_Reflection_Data.fstar_refl_binder in
      uu____196 rng l
let unembed_binders:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder Prims.list FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____211 = FStar_Syntax_Embeddings.unembed_list unembed_binder in
    uu____211 t
let embed_term:
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun rng  ->
    fun t  ->
      let t1 = protect_embedded_term FStar_Syntax_Syntax.tun t in
      let uu___255_227 = t1 in
      {
        FStar_Syntax_Syntax.n = (uu___255_227.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___255_227.FStar_Syntax_Syntax.vars)
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
      let uu____257 =
        let uu____258 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____258 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____257
    with
    | uu____265 ->
        ((let uu____267 =
            let uu____268 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded fvar: %s" uu____268 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____267);
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
      let uu____289 =
        let uu____290 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____290 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____289
    with
    | uu____297 ->
        ((let uu____299 =
            let uu____300 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded comp: %s" uu____300 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____299);
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
      let uu____321 =
        let uu____322 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____322 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____321
    with
    | uu____329 ->
        ((let uu____331 =
            let uu____332 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded env: %s" uu____332 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____331);
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
            let uu____341 =
              let uu____342 =
                let uu____343 =
                  let uu____344 =
                    let uu____345 = FStar_BigInt.string_of_big_int i in
                    FStar_Syntax_Util.exp_int uu____345 in
                  FStar_Syntax_Syntax.as_arg uu____344 in
                [uu____343] in
              FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
                uu____342 in
            uu____341 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____349 =
              let uu____350 =
                let uu____351 =
                  let uu____352 = FStar_Syntax_Embeddings.embed_string rng s in
                  FStar_Syntax_Syntax.as_arg uu____352 in
                [uu____351] in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String uu____350 in
            uu____349 FStar_Pervasives_Native.None FStar_Range.dummyRange in
      let uu___262_355 = r in
      {
        FStar_Syntax_Syntax.n = (uu___262_355.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___262_355.FStar_Syntax_Syntax.vars)
      }
let unembed_const:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____364 = FStar_Syntax_Util.head_and_args t1 in
    match uu____364 with
    | (hd1,args) ->
        let uu____403 =
          let uu____416 =
            let uu____417 = FStar_Syntax_Util.un_uinst hd1 in
            uu____417.FStar_Syntax_Syntax.n in
          (uu____416, args) in
        (match uu____403 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____477)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____502 = FStar_Syntax_Embeddings.unembed_int i in
             FStar_Util.bind_opt uu____502
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____511)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____536 = FStar_Syntax_Embeddings.unembed_string s in
             FStar_Util.bind_opt uu____536
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____543 ->
             ((let uu____557 =
                 let uu____558 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded vconst: %s" uu____558 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____557);
              FStar_Pervasives_Native.None))
let rec embed_pattern:
  FStar_Range.range ->
    FStar_Reflection_Data.pattern -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____566 =
            let uu____567 =
              let uu____568 =
                let uu____569 = embed_const rng c in
                FStar_Syntax_Syntax.as_arg uu____569 in
              [uu____568] in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant uu____567 in
          uu____566 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____578 =
            let uu____579 =
              let uu____580 =
                let uu____581 = embed_fvar rng fv in
                FStar_Syntax_Syntax.as_arg uu____581 in
              let uu____582 =
                let uu____585 =
                  let uu____586 =
                    let uu____587 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern in
                    uu____587 rng ps in
                  FStar_Syntax_Syntax.as_arg uu____586 in
                [uu____585] in
              uu____580 :: uu____582 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
              uu____579 in
          uu____578 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____598 =
            let uu____599 =
              let uu____600 =
                let uu____601 =
                  let uu____602 = FStar_Syntax_Syntax.mk_binder bv in
                  embed_binder rng uu____602 in
                FStar_Syntax_Syntax.as_arg uu____601 in
              [uu____600] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
              uu____599 in
          uu____598 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____606 =
            let uu____607 =
              let uu____608 =
                let uu____609 =
                  let uu____610 = FStar_Syntax_Syntax.mk_binder bv in
                  embed_binder rng uu____610 in
                FStar_Syntax_Syntax.as_arg uu____609 in
              [uu____608] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
              uu____607 in
          uu____606 FStar_Pervasives_Native.None rng
let rec unembed_pattern:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.pattern FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____621 = FStar_Syntax_Util.head_and_args t1 in
    match uu____621 with
    | (hd1,args) ->
        let uu____660 =
          let uu____673 =
            let uu____674 = FStar_Syntax_Util.un_uinst hd1 in
            uu____674.FStar_Syntax_Syntax.n in
          (uu____673, args) in
        (match uu____660 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____689)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____714 = unembed_const c in
             FStar_Util.bind_opt uu____714
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____723)::(ps,uu____725)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____760 = unembed_fvar f in
             FStar_Util.bind_opt uu____760
               (fun f1  ->
                  let uu____766 =
                    let uu____771 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern in
                    uu____771 ps in
                  FStar_Util.bind_opt uu____766
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____790)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____815 = unembed_binder b in
             FStar_Util.bind_opt uu____815
               (fun uu____821  ->
                  match uu____821 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                        (FStar_Reflection_Data.Pat_Var bv))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____830)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____855 = unembed_binder b in
             FStar_Util.bind_opt uu____855
               (fun uu____861  ->
                  match uu____861 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                        (FStar_Reflection_Data.Pat_Wild bv))
         | uu____868 ->
             ((let uu____882 =
                 let uu____883 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded pattern: %s" uu____883 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____882);
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
      let uu___263_908 = r in
      {
        FStar_Syntax_Syntax.n = (uu___263_908.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___263_908.FStar_Syntax_Syntax.vars)
      }
let unembed_aqualv:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____917 = FStar_Syntax_Util.head_and_args t1 in
    match uu____917 with
    | (hd1,args) ->
        let uu____956 =
          let uu____969 =
            let uu____970 = FStar_Syntax_Util.un_uinst hd1 in
            uu____970.FStar_Syntax_Syntax.n in
          (uu____969, args) in
        (match uu____956 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____1013 ->
             ((let uu____1027 =
                 let uu____1028 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded aqualv: %s" uu____1028 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____1027);
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
          let uu____1053 =
            let uu____1054 =
              let uu____1055 =
                let uu____1056 = embed_fvar rng fv in
                FStar_Syntax_Syntax.as_arg uu____1056 in
              [uu____1055] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
              uu____1054 in
          uu____1053 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1060 =
            let uu____1061 =
              let uu____1062 =
                let uu____1063 = embed_binder rng bv in
                FStar_Syntax_Syntax.as_arg uu____1063 in
              [uu____1062] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
              uu____1061 in
          uu____1060 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1068 =
            let uu____1069 =
              let uu____1070 =
                let uu____1071 = embed_term rng hd1 in
                FStar_Syntax_Syntax.as_arg uu____1071 in
              let uu____1072 =
                let uu____1075 =
                  let uu____1076 = embed_argv rng a in
                  FStar_Syntax_Syntax.as_arg uu____1076 in
                [uu____1075] in
              uu____1070 :: uu____1072 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
              uu____1069 in
          uu____1068 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1081 =
            let uu____1082 =
              let uu____1083 =
                let uu____1084 = embed_binder rng b in
                FStar_Syntax_Syntax.as_arg uu____1084 in
              let uu____1085 =
                let uu____1088 =
                  let uu____1089 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1089 in
                [uu____1088] in
              uu____1083 :: uu____1085 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
              uu____1082 in
          uu____1081 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1094 =
            let uu____1095 =
              let uu____1096 =
                let uu____1097 = embed_binder rng b in
                FStar_Syntax_Syntax.as_arg uu____1097 in
              let uu____1098 =
                let uu____1101 =
                  let uu____1102 = embed_comp rng c in
                  FStar_Syntax_Syntax.as_arg uu____1102 in
                [uu____1101] in
              uu____1096 :: uu____1098 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
              uu____1095 in
          uu____1094 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1106 =
            let uu____1107 =
              let uu____1108 =
                let uu____1109 = FStar_Syntax_Embeddings.embed_unit rng () in
                FStar_Syntax_Syntax.as_arg uu____1109 in
              [uu____1108] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
              uu____1107 in
          uu____1106 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1114 =
            let uu____1115 =
              let uu____1116 =
                let uu____1117 = embed_binder rng bv in
                FStar_Syntax_Syntax.as_arg uu____1117 in
              let uu____1118 =
                let uu____1121 =
                  let uu____1122 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1122 in
                [uu____1121] in
              uu____1116 :: uu____1118 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
              uu____1115 in
          uu____1114 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1126 =
            let uu____1127 =
              let uu____1128 =
                let uu____1129 = embed_const rng c in
                FStar_Syntax_Syntax.as_arg uu____1129 in
              [uu____1128] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
              uu____1127 in
          uu____1126 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____1134 =
            let uu____1135 =
              let uu____1136 =
                let uu____1137 = FStar_Syntax_Embeddings.embed_int rng u in
                FStar_Syntax_Syntax.as_arg uu____1137 in
              let uu____1138 =
                let uu____1141 =
                  let uu____1142 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1142 in
                [uu____1141] in
              uu____1136 :: uu____1138 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
              uu____1135 in
          uu____1134 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
          let uu____1148 =
            let uu____1149 =
              let uu____1150 =
                let uu____1151 = embed_binder rng b in
                FStar_Syntax_Syntax.as_arg uu____1151 in
              let uu____1152 =
                let uu____1155 =
                  let uu____1156 = embed_term rng t1 in
                  FStar_Syntax_Syntax.as_arg uu____1156 in
                let uu____1157 =
                  let uu____1160 =
                    let uu____1161 = embed_term rng t2 in
                    FStar_Syntax_Syntax.as_arg uu____1161 in
                  [uu____1160] in
                uu____1155 :: uu____1157 in
              uu____1150 :: uu____1152 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Let
              uu____1149 in
          uu____1148 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1170 =
            let uu____1171 =
              let uu____1172 =
                let uu____1173 = embed_term rng t1 in
                FStar_Syntax_Syntax.as_arg uu____1173 in
              let uu____1174 =
                let uu____1177 =
                  let uu____1178 =
                    let uu____1179 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch in
                    uu____1179 rng brs in
                  FStar_Syntax_Syntax.as_arg uu____1178 in
                [uu____1177] in
              uu____1172 :: uu____1174 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
              uu____1171 in
          uu____1170 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___264_1197 = FStar_Reflection_Data.ref_Tv_Unknown in
          {
            FStar_Syntax_Syntax.n = (uu___264_1197.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___264_1197.FStar_Syntax_Syntax.vars)
          }
let unembed_term_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1206 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1206 with
    | (hd1,args) ->
        let uu____1245 =
          let uu____1258 =
            let uu____1259 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1259.FStar_Syntax_Syntax.n in
          (uu____1258, args) in
        (match uu____1245 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1274)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1299 = unembed_binder b in
             FStar_Util.bind_opt uu____1299
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1308)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1333 = unembed_fvar f in
             FStar_Util.bind_opt uu____1333
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1342)::(r,uu____1344)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1379 = unembed_term l in
             FStar_Util.bind_opt uu____1379
               (fun l1  ->
                  let uu____1385 = unembed_argv r in
                  FStar_Util.bind_opt uu____1385
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1410)::(t2,uu____1412)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1447 = unembed_binder b in
             FStar_Util.bind_opt uu____1447
               (fun b1  ->
                  let uu____1453 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1453
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1462)::(t2,uu____1464)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1499 = unembed_binder b in
             FStar_Util.bind_opt uu____1499
               (fun b1  ->
                  let uu____1505 = unembed_comp t2 in
                  FStar_Util.bind_opt uu____1505
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1514)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             let uu____1539 = FStar_Syntax_Embeddings.unembed_unit u in
             FStar_Util.bind_opt uu____1539
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1548)::(t2,uu____1550)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1585 = unembed_binder b in
             FStar_Util.bind_opt uu____1585
               (fun b1  ->
                  let uu____1591 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1591
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1600)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1625 = unembed_const c in
             FStar_Util.bind_opt uu____1625
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1634)::(t2,uu____1636)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1671 = FStar_Syntax_Embeddings.unembed_int u in
             FStar_Util.bind_opt uu____1671
               (fun u1  ->
                  let uu____1677 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1677
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1686)::(t11,uu____1688)::(t2,uu____1690)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let_lid
             ->
             let uu____1735 = unembed_binder b in
             FStar_Util.bind_opt uu____1735
               (fun b1  ->
                  let uu____1741 = unembed_term t11 in
                  FStar_Util.bind_opt uu____1741
                    (fun t12  ->
                       let uu____1747 = unembed_term t2 in
                       FStar_Util.bind_opt uu____1747
                         (fun t21  ->
                            FStar_All.pipe_left
                              (fun _0_55  ->
                                 FStar_Pervasives_Native.Some _0_55)
                              (FStar_Reflection_Data.Tv_Let (b1, t12, t21)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1756)::(brs,uu____1758)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1793 = unembed_term t2 in
             FStar_Util.bind_opt uu____1793
               (fun t3  ->
                  let uu____1799 =
                    let uu____1808 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch in
                    uu____1808 brs in
                  FStar_Util.bind_opt uu____1799
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
         | uu____1862 ->
             ((let uu____1876 =
                 let uu____1877 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded term_view: %s"
                   uu____1877 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____1876);
              FStar_Pervasives_Native.None))
let embed_comp_view:
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total t ->
          let uu____1885 =
            let uu____1886 =
              let uu____1887 =
                let uu____1888 = embed_term rng t in
                FStar_Syntax_Syntax.as_arg uu____1888 in
              [uu____1887] in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Total
              uu____1886 in
          uu____1885 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
          let uu____1896 =
            let uu____1897 =
              let uu____1898 =
                let uu____1899 = embed_term rng pre in
                FStar_Syntax_Syntax.as_arg uu____1899 in
              let uu____1900 =
                let uu____1903 =
                  let uu____1904 = embed_term rng post1 in
                  FStar_Syntax_Syntax.as_arg uu____1904 in
                [uu____1903] in
              uu____1898 :: uu____1900 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Lemma
              uu____1897 in
          uu____1896 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___265_1907 = FStar_Reflection_Data.ref_C_Unknown in
          {
            FStar_Syntax_Syntax.n = (uu___265_1907.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___265_1907.FStar_Syntax_Syntax.vars)
          }
let unembed_comp_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1916 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1916 with
    | (hd1,args) ->
        let uu____1955 =
          let uu____1968 =
            let uu____1969 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1969.FStar_Syntax_Syntax.n in
          (uu____1968, args) in
        (match uu____1955 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____1984)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total_lid
             ->
             let uu____2009 = unembed_term t2 in
             FStar_Util.bind_opt uu____2009
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2018)::(post,uu____2020)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma_lid
             ->
             let uu____2055 = unembed_term pre in
             FStar_Util.bind_opt uu____2055
               (fun pre1  ->
                  let uu____2061 = unembed_term post in
                  FStar_Util.bind_opt uu____2061
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
         | uu____2085 ->
             ((let uu____2099 =
                 let uu____2100 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded comp_view: %s"
                   uu____2100 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____2099);
              FStar_Pervasives_Native.None))
let rec last: 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____2113::xs -> last xs
let rec init: 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____2137 = init xs in x :: uu____2137
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____2147 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____2147
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____2155 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____2155
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____2163) ->
        let uu____2176 = FStar_BigInt.big_int_of_string s in
        FStar_Reflection_Data.C_Int uu____2176
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____2178) ->
        FStar_Reflection_Data.C_String s
    | uu____2179 ->
        let uu____2180 =
          let uu____2181 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____2181 in
        failwith uu____2180
let rec inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let t2 = FStar_Syntax_Util.un_uinst t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____2188) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2194 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____2194
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2237 = last args in
        (match uu____2237 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____2257) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit in
             let uu____2258 =
               let uu____2263 =
                 let uu____2266 =
                   let uu____2267 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2267 in
                 uu____2266 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos in
               (uu____2263, (a, q')) in
             FStar_Reflection_Data.Tv_App uu____2258)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2286,uu____2287) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____2329 = FStar_Syntax_Subst.open_term bs t3 in
        (match uu____2329 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2356 =
                    let uu____2361 = FStar_Syntax_Util.abs bs2 t4 k in
                    (b, uu____2361) in
                  FStar_Reflection_Data.Tv_Abs uu____2356))
    | FStar_Syntax_Syntax.Tm_type uu____2366 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____2382 ->
        let uu____2395 = FStar_Syntax_Util.arrow_one t2 in
        (match uu____2395 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____2419 = FStar_Syntax_Subst.open_term [b] t3 in
        (match uu____2419 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2448 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2458 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____2458
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____2485 =
          let uu____2490 =
            let uu____2491 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_BigInt.of_int_fs uu____2491 in
          (uu____2490, t3) in
        FStar_Reflection_Data.Tv_Uvar uu____2485
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2511 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____2514 = FStar_Syntax_Subst.open_term [b] t21 in
               (match uu____2514 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____2543 ->
                          failwith
                            "impossible: open_term returned different amount of binders" in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2601 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____2601
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2620 =
                let uu____2627 =
                  FStar_List.map
                    (fun uu____2639  ->
                       match uu____2639 with
                       | (p1,uu____2647) -> inspect_pat p1) ps in
                (fv, uu____2627) in
              FStar_Reflection_Data.Pat_Cons uu____2620
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2656 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___251_2700  ->
               match uu___251_2700 with
               | (pat,uu____2722,t4) ->
                   let uu____2740 = inspect_pat pat in (uu____2740, t4)) brs1 in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2753 ->
        ((let uu____2755 = FStar_Syntax_Print.tag_of_term t2 in
          let uu____2756 = FStar_Syntax_Print.term_to_string t2 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____2755 uu____2756);
         FStar_Reflection_Data.Tv_Unknown)
let inspect_comp: FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2761) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2772)::(post,uu____2774)::uu____2775 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2808 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____2818 ->
        FStar_Reflection_Data.C_Unknown
let pack_comp: FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____2831 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2836 =
          let uu____2847 = FStar_BigInt.string_of_big_int i in
          (uu____2847, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____2836
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2863) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2872 =
               let uu____2881 = FStar_Syntax_Syntax.as_arg r in [uu____2881] in
             FStar_Syntax_Util.mk_app l uu____2872
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2882 =
               let uu____2891 = FStar_Syntax_Syntax.iarg r in [uu____2891] in
             FStar_Syntax_Util.mk_app l uu____2882)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2897),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2904 =
          let uu____2907 =
            let uu____2908 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____2908 in
          FStar_Syntax_Syntax.mk uu____2907 in
        uu____2904 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____2914 = FStar_BigInt.to_int_fs u in
        FStar_Syntax_Util.uvar_from_id uu____2914 t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 in
        let uu____2920 =
          let uu____2923 =
            let uu____2924 =
              let uu____2937 = FStar_Syntax_Subst.close [b] t2 in
              ((false, [lb]), uu____2937) in
            FStar_Syntax_Syntax.Tm_let uu____2924 in
          FStar_Syntax_Syntax.mk uu____2923 in
        uu____2920 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____2966 =
                let uu____2967 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____2967 in
              FStar_All.pipe_left wrap uu____2966
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2976 =
                let uu____2977 =
                  let uu____2990 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____3004 = pack_pat p1 in (uu____3004, false))
                      ps in
                  (fv, uu____2990) in
                FStar_Syntax_Syntax.Pat_cons uu____2977 in
              FStar_All.pipe_left wrap uu____2976
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___252_3050  ->
               match uu___252_3050 with
               | (pat,t1) ->
                   let uu____3067 = pack_pat pat in
                   (uu____3067, FStar_Pervasives_Native.None, t1)) brs in
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
      let uu___266_3086 = r in
      {
        FStar_Syntax_Syntax.n = (uu___266_3086.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___266_3086.FStar_Syntax_Syntax.vars)
      }
let unembed_order:
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3095 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3095 with
    | (hd1,args) ->
        let uu____3134 =
          let uu____3147 =
            let uu____3148 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3148.FStar_Syntax_Syntax.n in
          (uu____3147, args) in
        (match uu____3134 with
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
         | uu____3206 ->
             ((let uu____3220 =
                 let uu____3221 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded order: %s" uu____3221 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____3220);
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____3287,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____3388,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____3405 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____3405 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____3478,n1,uu____3480) ->
                          let uu____3485 =
                            let uu____3490 = FStar_Ident.path_of_lid lid2 in
                            (uu____3490, t1) in
                          FStar_Reflection_Data.Ctor uu____3485
                      | uu____3495 -> failwith "wat 1")
                 | uu____3496 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3525) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____3540 ->
                     failwith "global Sig_let has bv" in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____3545 -> FStar_Reflection_Data.Unk)
let embed_ctor:
  FStar_Range.range -> FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun c  ->
      match c with
      | FStar_Reflection_Data.Ctor (nm,t) ->
          let uu____3554 =
            let uu____3555 =
              let uu____3556 =
                let uu____3557 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm in
                FStar_Syntax_Syntax.as_arg uu____3557 in
              let uu____3558 =
                let uu____3561 =
                  let uu____3562 = embed_term rng t in
                  FStar_Syntax_Syntax.as_arg uu____3562 in
                [uu____3561] in
              uu____3556 :: uu____3558 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
              uu____3555 in
          uu____3554 FStar_Pervasives_Native.None rng
let unembed_ctor:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.ctor FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3573 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3573 with
    | (hd1,args) ->
        let uu____3612 =
          let uu____3625 =
            let uu____3626 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3626.FStar_Syntax_Syntax.n in
          (uu____3625, args) in
        (match uu____3612 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3641)::(t2,uu____3643)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____3678 = FStar_Syntax_Embeddings.unembed_string_list nm in
             FStar_Util.bind_opt uu____3678
               (fun nm1  ->
                  let uu____3690 = unembed_term t2 in
                  FStar_Util.bind_opt uu____3690
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                         (FStar_Reflection_Data.Ctor (nm1, t3))))
         | uu____3699 ->
             ((let uu____3713 =
                 let uu____3714 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded ctor: %s" uu____3714 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____3713);
              FStar_Pervasives_Native.None))
let embed_sigelt_view:
  FStar_Range.range ->
    FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun sev  ->
      match sev with
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____3733 =
            let uu____3734 =
              let uu____3735 =
                let uu____3736 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm in
                FStar_Syntax_Syntax.as_arg uu____3736 in
              let uu____3737 =
                let uu____3740 =
                  let uu____3741 = embed_binders rng bs in
                  FStar_Syntax_Syntax.as_arg uu____3741 in
                let uu____3742 =
                  let uu____3745 =
                    let uu____3746 = embed_term rng t in
                    FStar_Syntax_Syntax.as_arg uu____3746 in
                  let uu____3747 =
                    let uu____3750 =
                      let uu____3751 =
                        let uu____3752 =
                          FStar_Syntax_Embeddings.embed_list embed_ctor
                            FStar_Reflection_Data.fstar_refl_ctor in
                        uu____3752 rng dcs in
                      FStar_Syntax_Syntax.as_arg uu____3751 in
                    [uu____3750] in
                  uu____3745 :: uu____3747 in
                uu____3740 :: uu____3742 in
              uu____3735 :: uu____3737 in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive uu____3734 in
          uu____3733 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
          let uu____3765 =
            let uu____3766 =
              let uu____3767 =
                let uu____3768 = embed_fvar rng fv in
                FStar_Syntax_Syntax.as_arg uu____3768 in
              let uu____3769 =
                let uu____3772 =
                  let uu____3773 = embed_term rng ty in
                  FStar_Syntax_Syntax.as_arg uu____3773 in
                let uu____3774 =
                  let uu____3777 =
                    let uu____3778 = embed_term rng t in
                    FStar_Syntax_Syntax.as_arg uu____3778 in
                  [uu____3777] in
                uu____3772 :: uu____3774 in
              uu____3767 :: uu____3769 in
            FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Let
              uu____3766 in
          uu____3765 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___267_3781 = FStar_Reflection_Data.ref_Unk in
          {
            FStar_Syntax_Syntax.n = (uu___267_3781.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___267_3781.FStar_Syntax_Syntax.vars)
          }
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3790 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3790 with
    | (hd1,args) ->
        let uu____3829 =
          let uu____3842 =
            let uu____3843 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3843.FStar_Syntax_Syntax.n in
          (uu____3842, args) in
        (match uu____3829 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3858)::(bs,uu____3860)::(t2,uu____3862)::(dcs,uu____3864)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3919 = FStar_Syntax_Embeddings.unembed_string_list nm in
             FStar_Util.bind_opt uu____3919
               (fun nm1  ->
                  let uu____3931 = unembed_binders bs in
                  FStar_Util.bind_opt uu____3931
                    (fun bs1  ->
                       let uu____3943 = unembed_term t2 in
                       FStar_Util.bind_opt uu____3943
                         (fun t3  ->
                            let uu____3949 =
                              let uu____3954 =
                                FStar_Syntax_Embeddings.unembed_list
                                  unembed_ctor in
                              uu____3954 dcs in
                            FStar_Util.bind_opt uu____3949
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____3977)::(ty,uu____3979)::(t2,uu____3981)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let_lid
             ->
             let uu____4026 = unembed_fvar fvar1 in
             FStar_Util.bind_opt uu____4026
               (fun fvar2  ->
                  let uu____4032 = unembed_term ty in
                  FStar_Util.bind_opt uu____4032
                    (fun ty1  ->
                       let uu____4038 = unembed_term t2 in
                       FStar_Util.bind_opt uu____4038
                         (fun t3  ->
                            FStar_All.pipe_left
                              (fun _0_63  ->
                                 FStar_Pervasives_Native.Some _0_63)
                              (FStar_Reflection_Data.Sg_Let (fvar2, ty1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____4060 ->
             ((let uu____4074 =
                 let uu____4075 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded sigelt_view: %s"
                   uu____4075 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____4074);
              FStar_Pervasives_Native.None))
let binders_of_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders
  = fun e  -> FStar_TypeChecker_Env.all_binders e
let type_of_binder:
  'Auu____4081 .
    (FStar_Syntax_Syntax.bv,'Auu____4081) FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun b  -> match b with | (b1,uu____4097) -> b1.FStar_Syntax_Syntax.sort
let term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  FStar_Syntax_Util.term_eq
let fresh_binder:
  'Auu____4104 .
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.bv,'Auu____4104 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____4115 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t in
    (uu____4115, FStar_Pervasives_Native.None)
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  FStar_Syntax_Print.term_to_string