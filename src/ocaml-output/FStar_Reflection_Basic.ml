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
let embed_binder: FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term =
  fun b  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_binder b
      "reflection.embed_binder" FStar_Pervasives_Native.None
let unembed_binder:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____177 =
        let uu____178 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____178 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____177
    with
    | uu____185 ->
        ((let uu____187 =
            let uu____188 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded binder: %s" uu____188 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____187);
         FStar_Pervasives_Native.None)
let embed_binders:
  FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term =
  fun l  ->
    FStar_Syntax_Embeddings.embed_list embed_binder
      FStar_Reflection_Data.fstar_refl_binder l
let unembed_binders:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder Prims.list FStar_Pervasives_Native.option
  = fun t  -> FStar_Syntax_Embeddings.unembed_list unembed_binder t
let embed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> protect_embedded_term FStar_Syntax_Syntax.tun t
let unembed_term:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  = fun t  -> un_protect_embedded_term t
let embed_fvar: FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun fv  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_fvar fv
      "reflection.embed_fvar" FStar_Pervasives_Native.None
let unembed_fvar:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____236 =
        let uu____237 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____237 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____236
    with
    | uu____244 ->
        ((let uu____246 =
            let uu____247 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded fvar: %s" uu____247 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____246);
         FStar_Pervasives_Native.None)
let embed_comp: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term =
  fun c  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_comp c
      "reflection.embed_comp" FStar_Pervasives_Native.None
let unembed_comp:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option
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
            let uu____278 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded comp: %s" uu____278 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____277);
         FStar_Pervasives_Native.None)
let embed_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term =
  fun env  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_env env
      "tactics_embed_env" FStar_Pervasives_Native.None
let unembed_env:
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____298 =
        let uu____299 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____299 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____298
    with
    | uu____306 ->
        ((let uu____308 =
            let uu____309 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded env: %s" uu____309 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____308);
         FStar_Pervasives_Native.None)
let embed_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
    | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
    | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
    | FStar_Reflection_Data.C_Int i ->
        let uu____315 =
          let uu____316 =
            let uu____317 =
              let uu____318 =
                let uu____319 = FStar_Util.string_of_int i in
                FStar_Syntax_Util.exp_int uu____319 in
              FStar_Syntax_Syntax.as_arg uu____318 in
            [uu____317] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____316 in
        uu____315 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_String s ->
        let uu____323 =
          let uu____324 =
            let uu____325 =
              let uu____326 = FStar_Syntax_Embeddings.embed_string s in
              FStar_Syntax_Syntax.as_arg uu____326 in
            [uu____325] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String
            uu____324 in
        uu____323 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_const:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____338 = FStar_Syntax_Util.head_and_args t1 in
    match uu____338 with
    | (hd1,args) ->
        let uu____377 =
          let uu____390 =
            let uu____391 = FStar_Syntax_Util.un_uinst hd1 in
            uu____391.FStar_Syntax_Syntax.n in
          (uu____390, args) in
        (match uu____377 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____451)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____476 = FStar_Syntax_Embeddings.unembed_int i in
             FStar_Util.bind_opt uu____476
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____485)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____510 = FStar_Syntax_Embeddings.unembed_string s in
             FStar_Util.bind_opt uu____510
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.C_String s1))
         | uu____517 ->
             ((let uu____531 =
                 let uu____532 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded vconst: %s" uu____532 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____531);
              FStar_Pervasives_Native.None))
let rec embed_pattern:
  FStar_Reflection_Data.pattern -> FStar_Syntax_Syntax.term =
  fun p  ->
    match p with
    | FStar_Reflection_Data.Pat_Constant c ->
        let uu____538 =
          let uu____539 =
            let uu____540 =
              let uu____541 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____541 in
            [uu____540] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant uu____539 in
        uu____538 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
        let uu____550 =
          let uu____551 =
            let uu____552 =
              let uu____553 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____553 in
            let uu____554 =
              let uu____557 =
                let uu____558 =
                  FStar_Syntax_Embeddings.embed_list embed_pattern
                    FStar_Reflection_Data.fstar_refl_pattern ps in
                FStar_Syntax_Syntax.as_arg uu____558 in
              [uu____557] in
            uu____552 :: uu____554 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
            uu____551 in
        uu____550 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Var bv ->
        let uu____562 =
          let uu____563 =
            let uu____564 =
              let uu____565 =
                let uu____566 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____566 in
              FStar_Syntax_Syntax.as_arg uu____565 in
            [uu____564] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
            uu____563 in
        uu____562 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Wild bv ->
        let uu____570 =
          let uu____571 =
            let uu____572 =
              let uu____573 =
                let uu____574 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____574 in
              FStar_Syntax_Syntax.as_arg uu____573 in
            [uu____572] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
            uu____571 in
        uu____570 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_pattern:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.pattern FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____586 = FStar_Syntax_Util.head_and_args t1 in
    match uu____586 with
    | (hd1,args) ->
        let uu____625 =
          let uu____638 =
            let uu____639 = FStar_Syntax_Util.un_uinst hd1 in
            uu____639.FStar_Syntax_Syntax.n in
          (uu____638, args) in
        (match uu____625 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____654)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____679 = unembed_const c in
             FStar_Util.bind_opt uu____679
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____688)::(ps,uu____690)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____725 = unembed_fvar f in
             FStar_Util.bind_opt uu____725
               (fun f1  ->
                  let uu____731 =
                    FStar_Syntax_Embeddings.unembed_list unembed_pattern ps in
                  FStar_Util.bind_opt uu____731
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____748)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____773 = unembed_binder b in
             FStar_Util.bind_opt uu____773
               (fun uu____779  ->
                  match uu____779 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                        (FStar_Reflection_Data.Pat_Var bv))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____788)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____813 = unembed_binder b in
             FStar_Util.bind_opt uu____813
               (fun uu____819  ->
                  match uu____819 with
                  | (bv,aq) ->
                      FStar_All.pipe_left
                        (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                        (FStar_Reflection_Data.Pat_Wild bv))
         | uu____826 ->
             ((let uu____840 =
                 let uu____841 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded pattern: %s" uu____841 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____840);
              FStar_Pervasives_Native.None))
let embed_branch:
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  FStar_Syntax_Embeddings.embed_pair embed_pattern
    FStar_Reflection_Data.fstar_refl_pattern embed_term
    FStar_Syntax_Syntax.t_term
let unembed_branch:
  FStar_Syntax_Syntax.term ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  = FStar_Syntax_Embeddings.unembed_pair unembed_pattern unembed_term
let embed_aqualv: FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.term =
  fun q  ->
    match q with
    | FStar_Reflection_Data.Q_Explicit  ->
        FStar_Reflection_Data.ref_Q_Explicit
    | FStar_Reflection_Data.Q_Implicit  ->
        FStar_Reflection_Data.ref_Q_Implicit
let unembed_aqualv:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____871 = FStar_Syntax_Util.head_and_args t1 in
    match uu____871 with
    | (hd1,args) ->
        let uu____910 =
          let uu____923 =
            let uu____924 = FStar_Syntax_Util.un_uinst hd1 in
            uu____924.FStar_Syntax_Syntax.n in
          (uu____923, args) in
        (match uu____910 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____967 ->
             ((let uu____981 =
                 let uu____982 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded aqualv: %s" uu____982 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____981);
              FStar_Pervasives_Native.None))
let embed_argv:
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  FStar_Syntax_Embeddings.embed_pair embed_term FStar_Syntax_Syntax.t_term
    embed_aqualv FStar_Reflection_Data.fstar_refl_aqualv
let unembed_argv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  = FStar_Syntax_Embeddings.unembed_pair unembed_term unembed_aqualv
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____1004 =
          let uu____1005 =
            let uu____1006 =
              let uu____1007 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____1007 in
            [uu____1006] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____1005 in
        uu____1004 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____1011 =
          let uu____1012 =
            let uu____1013 =
              let uu____1014 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1014 in
            [uu____1013] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____1012 in
        uu____1011 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____1019 =
          let uu____1020 =
            let uu____1021 =
              let uu____1022 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____1022 in
            let uu____1023 =
              let uu____1026 =
                let uu____1027 = embed_argv a in
                FStar_Syntax_Syntax.as_arg uu____1027 in
              [uu____1026] in
            uu____1021 :: uu____1023 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____1020 in
        uu____1019 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____1032 =
          let uu____1033 =
            let uu____1034 =
              let uu____1035 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1035 in
            let uu____1036 =
              let uu____1039 =
                let uu____1040 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1040 in
              [uu____1039] in
            uu____1034 :: uu____1036 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____1033 in
        uu____1032 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____1045 =
          let uu____1046 =
            let uu____1047 =
              let uu____1048 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1048 in
            let uu____1049 =
              let uu____1052 =
                let uu____1053 = embed_comp c in
                FStar_Syntax_Syntax.as_arg uu____1053 in
              [uu____1052] in
            uu____1047 :: uu____1049 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____1046 in
        uu____1045 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____1057 =
          let uu____1058 =
            let uu____1059 =
              let uu____1060 = FStar_Syntax_Embeddings.embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____1060 in
            [uu____1059] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____1058 in
        uu____1057 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____1065 =
          let uu____1066 =
            let uu____1067 =
              let uu____1068 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1068 in
            let uu____1069 =
              let uu____1072 =
                let uu____1073 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1073 in
              [uu____1072] in
            uu____1067 :: uu____1069 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____1066 in
        uu____1065 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____1077 =
          let uu____1078 =
            let uu____1079 =
              let uu____1080 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____1080 in
            [uu____1079] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____1078 in
        uu____1077 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____1085 =
          let uu____1086 =
            let uu____1087 =
              let uu____1088 = FStar_Syntax_Embeddings.embed_int u in
              FStar_Syntax_Syntax.as_arg uu____1088 in
            let uu____1089 =
              let uu____1092 =
                let uu____1093 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1093 in
              [uu____1092] in
            uu____1087 :: uu____1089 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____1086 in
        uu____1085 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let uu____1099 =
          let uu____1100 =
            let uu____1101 =
              let uu____1102 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1102 in
            let uu____1103 =
              let uu____1106 =
                let uu____1107 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1107 in
              let uu____1108 =
                let uu____1111 =
                  let uu____1112 = embed_term t2 in
                  FStar_Syntax_Syntax.as_arg uu____1112 in
                [uu____1111] in
              uu____1106 :: uu____1108 in
            uu____1101 :: uu____1103 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Let
            uu____1100 in
        uu____1099 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t1,brs) ->
        let uu____1121 =
          let uu____1122 =
            let uu____1123 =
              let uu____1124 = embed_term t1 in
              FStar_Syntax_Syntax.as_arg uu____1124 in
            let uu____1125 =
              let uu____1128 =
                let uu____1129 =
                  FStar_Syntax_Embeddings.embed_list embed_branch
                    FStar_Reflection_Data.fstar_refl_branch brs in
                FStar_Syntax_Syntax.as_arg uu____1129 in
              [uu____1128] in
            uu____1123 :: uu____1125 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
            uu____1122 in
        uu____1121 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_term_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1145 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1145 with
    | (hd1,args) ->
        let uu____1184 =
          let uu____1197 =
            let uu____1198 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1198.FStar_Syntax_Syntax.n in
          (uu____1197, args) in
        (match uu____1184 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1213)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1238 = unembed_binder b in
             FStar_Util.bind_opt uu____1238
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1247)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1272 = unembed_fvar f in
             FStar_Util.bind_opt uu____1272
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1281)::(r,uu____1283)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1318 = unembed_term l in
             FStar_Util.bind_opt uu____1318
               (fun l1  ->
                  let uu____1324 = unembed_argv r in
                  FStar_Util.bind_opt uu____1324
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1349)::(t2,uu____1351)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1386 = unembed_binder b in
             FStar_Util.bind_opt uu____1386
               (fun b1  ->
                  let uu____1392 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1392
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1401)::(t2,uu____1403)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1438 = unembed_binder b in
             FStar_Util.bind_opt uu____1438
               (fun b1  ->
                  let uu____1444 = unembed_comp t2 in
                  FStar_Util.bind_opt uu____1444
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1453)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             let uu____1478 = FStar_Syntax_Embeddings.unembed_unit u in
             FStar_Util.bind_opt uu____1478
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1487)::(t2,uu____1489)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1524 = unembed_binder b in
             FStar_Util.bind_opt uu____1524
               (fun b1  ->
                  let uu____1530 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1530
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1539)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1564 = unembed_const c in
             FStar_Util.bind_opt uu____1564
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1573)::(t2,uu____1575)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1610 = FStar_Syntax_Embeddings.unembed_int u in
             FStar_Util.bind_opt uu____1610
               (fun u1  ->
                  let uu____1616 = unembed_term t2 in
                  FStar_Util.bind_opt uu____1616
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_55  -> FStar_Pervasives_Native.Some _0_55)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1625)::(t11,uu____1627)::(t2,uu____1629)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let_lid
             ->
             let uu____1674 = unembed_binder b in
             FStar_Util.bind_opt uu____1674
               (fun b1  ->
                  let uu____1680 = unembed_term t11 in
                  FStar_Util.bind_opt uu____1680
                    (fun t12  ->
                       let uu____1686 = unembed_term t2 in
                       FStar_Util.bind_opt uu____1686
                         (fun t21  ->
                            FStar_All.pipe_left
                              (fun _0_56  ->
                                 FStar_Pervasives_Native.Some _0_56)
                              (FStar_Reflection_Data.Tv_Let (b1, t12, t21)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1695)::(brs,uu____1697)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1732 = unembed_term t2 in
             FStar_Util.bind_opt uu____1732
               (fun t3  ->
                  let uu____1738 =
                    FStar_Syntax_Embeddings.unembed_list unembed_branch brs in
                  FStar_Util.bind_opt uu____1738
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
         | uu____1790 ->
             ((let uu____1804 =
                 let uu____1805 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded term_view: %s"
                   uu____1805 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____1804);
              FStar_Pervasives_Native.None))
let embed_comp_view:
  FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t ->
        let uu____1811 =
          let uu____1812 =
            let uu____1813 =
              let uu____1814 = embed_term t in
              FStar_Syntax_Syntax.as_arg uu____1814 in
            [uu____1813] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Total
            uu____1812 in
        uu____1811 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
        let uu____1822 =
          let uu____1823 =
            let uu____1824 =
              let uu____1825 = embed_term pre in
              FStar_Syntax_Syntax.as_arg uu____1825 in
            let uu____1826 =
              let uu____1829 =
                let uu____1830 = embed_term post1 in
                FStar_Syntax_Syntax.as_arg uu____1830 in
              [uu____1829] in
            uu____1824 :: uu____1826 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Lemma
            uu____1823 in
        uu____1822 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_Unknown  -> FStar_Reflection_Data.ref_C_Unknown
let unembed_comp_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1842 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1842 with
    | (hd1,args) ->
        let uu____1881 =
          let uu____1894 =
            let uu____1895 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1895.FStar_Syntax_Syntax.n in
          (uu____1894, args) in
        (match uu____1881 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____1910)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total_lid
             ->
             let uu____1935 = unembed_term t2 in
             FStar_Util.bind_opt uu____1935
               (fun t3  ->
                  FStar_All.pipe_left
                    (fun _0_59  -> FStar_Pervasives_Native.Some _0_59)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____1944)::(post,uu____1946)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma_lid
             ->
             let uu____1981 = unembed_term pre in
             FStar_Util.bind_opt uu____1981
               (fun pre1  ->
                  let uu____1987 = unembed_term post in
                  FStar_Util.bind_opt uu____1987
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
         | uu____2011 ->
             ((let uu____2025 =
                 let uu____2026 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded comp_view: %s"
                   uu____2026 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____2025);
              FStar_Pervasives_Native.None))
let rec last: 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____2041::xs -> last xs
let rec init: 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____2067 = init xs in x :: uu____2067
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____2078 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____2078
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____2087 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____2087
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____2097) ->
        let uu____2110 = FStar_Util.int_of_string s in
        FStar_Reflection_Data.C_Int uu____2110
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____2112) ->
        FStar_Reflection_Data.C_String s
    | uu____2113 ->
        let uu____2114 =
          let uu____2115 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____2115 in
        failwith uu____2114
let rec inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let t2 = FStar_Syntax_Util.un_uinst t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____2123) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2129 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____2129
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2172 = last args in
        (match uu____2172 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____2192) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit in
             let uu____2193 =
               let uu____2198 =
                 let uu____2201 =
                   let uu____2202 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2202 in
                 uu____2201 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos in
               (uu____2198, (a, q')) in
             FStar_Reflection_Data.Tv_App uu____2193)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2221,uu____2222) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____2264 = FStar_Syntax_Subst.open_term bs t3 in
        (match uu____2264 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2291 =
                    let uu____2296 = FStar_Syntax_Util.abs bs2 t4 k in
                    (b, uu____2296) in
                  FStar_Reflection_Data.Tv_Abs uu____2291))
    | FStar_Syntax_Syntax.Tm_type uu____2301 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____2317 ->
        let uu____2330 = FStar_Syntax_Util.arrow_one t2 in
        (match uu____2330 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____2354 = FStar_Syntax_Subst.open_term [b] t3 in
        (match uu____2354 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2383 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2393 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____2393
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____2420 =
          let uu____2425 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____2425, t3) in
        FStar_Reflection_Data.Tv_Uvar uu____2420
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2445 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____2448 = FStar_Syntax_Subst.open_term [b] t21 in
               (match uu____2448 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____2477 ->
                          failwith
                            "impossible: open_term returned different amount of binders" in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2535 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____2535
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2554 =
                let uu____2561 =
                  FStar_List.map
                    (fun uu____2573  ->
                       match uu____2573 with
                       | (p1,uu____2581) -> inspect_pat p1) ps in
                (fv, uu____2561) in
              FStar_Reflection_Data.Pat_Cons uu____2554
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2590 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___111_2634  ->
               match uu___111_2634 with
               | (pat,uu____2656,t4) ->
                   let uu____2674 = inspect_pat pat in (uu____2674, t4)) brs1 in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2687 ->
        ((let uu____2689 = FStar_Syntax_Print.tag_of_term t2 in
          let uu____2690 = FStar_Syntax_Print.term_to_string t2 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____2689 uu____2690);
         FStar_Reflection_Data.Tv_Unknown)
let inspect_comp: FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2696) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2707)::(post,uu____2709)::uu____2710 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2743 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____2753 ->
        FStar_Reflection_Data.C_Unknown
let pack_comp: FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____2767 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2773 =
          let uu____2784 = FStar_Util.string_of_int i in
          (uu____2784, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____2773
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2801) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2810 =
               let uu____2819 = FStar_Syntax_Syntax.as_arg r in [uu____2819] in
             FStar_Syntax_Util.mk_app l uu____2810
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2820 =
               let uu____2829 = FStar_Syntax_Syntax.iarg r in [uu____2829] in
             FStar_Syntax_Util.mk_app l uu____2820)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2835),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2842 =
          let uu____2845 =
            let uu____2846 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____2846 in
          FStar_Syntax_Syntax.mk uu____2845 in
        uu____2842 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        FStar_Syntax_Util.uvar_from_id u t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 in
        let uu____2857 =
          let uu____2860 =
            let uu____2861 =
              let uu____2874 = FStar_Syntax_Subst.close [b] t2 in
              ((false, [lb]), uu____2874) in
            FStar_Syntax_Syntax.Tm_let uu____2861 in
          FStar_Syntax_Syntax.mk uu____2860 in
        uu____2857 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____2903 =
                let uu____2904 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____2904 in
              FStar_All.pipe_left wrap uu____2903
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2913 =
                let uu____2914 =
                  let uu____2927 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2941 = pack_pat p1 in (uu____2941, false))
                      ps in
                  (fv, uu____2927) in
                FStar_Syntax_Syntax.Pat_cons uu____2914 in
              FStar_All.pipe_left wrap uu____2913
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___112_2987  ->
               match uu___112_2987 with
               | (pat,t1) ->
                   let uu____3004 = pack_pat pat in
                   (uu____3004, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        failwith "pack: unexpected term view"
let embed_order: FStar_Order.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order:
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3029 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3029 with
    | (hd1,args) ->
        let uu____3068 =
          let uu____3081 =
            let uu____3082 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3082.FStar_Syntax_Syntax.n in
          (uu____3081, args) in
        (match uu____3068 with
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
         | uu____3140 ->
             ((let uu____3154 =
                 let uu____3155 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded order: %s" uu____3155 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____3154);
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
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____3227,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____3328,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____3345 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____3345 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____3418,n1,uu____3420) ->
                          let uu____3425 =
                            let uu____3430 = FStar_Ident.path_of_lid lid2 in
                            (uu____3430, t1) in
                          FStar_Reflection_Data.Ctor uu____3425
                      | uu____3435 -> failwith "wat 1")
                 | uu____3436 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3465) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____3480 ->
                     failwith "global Sig_let has bv" in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____3485 -> FStar_Reflection_Data.Unk)
let embed_ctor: FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____3492 =
          let uu____3493 =
            let uu____3494 =
              let uu____3495 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____3495 in
            let uu____3496 =
              let uu____3499 =
                let uu____3500 = embed_term t in
                FStar_Syntax_Syntax.as_arg uu____3500 in
              [uu____3499] in
            uu____3494 :: uu____3496 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____3493 in
        uu____3492 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_ctor:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.ctor FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3512 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3512 with
    | (hd1,args) ->
        let uu____3551 =
          let uu____3564 =
            let uu____3565 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3565.FStar_Syntax_Syntax.n in
          (uu____3564, args) in
        (match uu____3551 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3580)::(t2,uu____3582)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____3617 = FStar_Syntax_Embeddings.unembed_string_list nm in
             FStar_Util.bind_opt uu____3617
               (fun nm1  ->
                  let uu____3629 = unembed_term t2 in
                  FStar_Util.bind_opt uu____3629
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_62  -> FStar_Pervasives_Native.Some _0_62)
                         (FStar_Reflection_Data.Ctor (nm1, t3))))
         | uu____3638 ->
             ((let uu____3652 =
                 let uu____3653 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded ctor: %s" uu____3653 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____3652);
              FStar_Pervasives_Native.None))
let embed_sigelt_view:
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____3670 =
          let uu____3671 =
            let uu____3672 =
              let uu____3673 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____3673 in
            let uu____3674 =
              let uu____3677 =
                let uu____3678 = embed_binders bs in
                FStar_Syntax_Syntax.as_arg uu____3678 in
              let uu____3679 =
                let uu____3682 =
                  let uu____3683 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____3683 in
                let uu____3684 =
                  let uu____3687 =
                    let uu____3688 =
                      FStar_Syntax_Embeddings.embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs in
                    FStar_Syntax_Syntax.as_arg uu____3688 in
                  [uu____3687] in
                uu____3682 :: uu____3684 in
              uu____3677 :: uu____3679 in
            uu____3672 :: uu____3674 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____3671 in
        uu____3670 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
        let uu____3694 =
          let uu____3695 =
            let uu____3696 =
              let uu____3697 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____3697 in
            let uu____3698 =
              let uu____3701 =
                let uu____3702 = embed_term ty in
                FStar_Syntax_Syntax.as_arg uu____3702 in
              let uu____3703 =
                let uu____3706 =
                  let uu____3707 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____3707 in
                [uu____3706] in
              uu____3701 :: uu____3703 in
            uu____3696 :: uu____3698 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Let
            uu____3695 in
        uu____3694 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3719 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3719 with
    | (hd1,args) ->
        let uu____3758 =
          let uu____3771 =
            let uu____3772 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3772.FStar_Syntax_Syntax.n in
          (uu____3771, args) in
        (match uu____3758 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3787)::(bs,uu____3789)::(t2,uu____3791)::(dcs,uu____3793)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3848 = FStar_Syntax_Embeddings.unembed_string_list nm in
             FStar_Util.bind_opt uu____3848
               (fun nm1  ->
                  let uu____3860 = unembed_binders bs in
                  FStar_Util.bind_opt uu____3860
                    (fun bs1  ->
                       let uu____3872 = unembed_term t2 in
                       FStar_Util.bind_opt uu____3872
                         (fun t3  ->
                            let uu____3878 =
                              FStar_Syntax_Embeddings.unembed_list
                                unembed_ctor dcs in
                            FStar_Util.bind_opt uu____3878
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_Pervasives_Native.Some _0_63)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____3899)::(ty,uu____3901)::(t2,uu____3903)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let_lid
             ->
             let uu____3948 = unembed_fvar fvar1 in
             FStar_Util.bind_opt uu____3948
               (fun fvar2  ->
                  let uu____3954 = unembed_term ty in
                  FStar_Util.bind_opt uu____3954
                    (fun ty1  ->
                       let uu____3960 = unembed_term t2 in
                       FStar_Util.bind_opt uu____3960
                         (fun t3  ->
                            FStar_All.pipe_left
                              (fun _0_64  ->
                                 FStar_Pervasives_Native.Some _0_64)
                              (FStar_Reflection_Data.Sg_Let (fvar2, ty1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____3982 ->
             ((let uu____3996 =
                 let uu____3997 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1 "Not an embedded sigelt_view: %s"
                   uu____3997 in
               FStar_Errors.warn t1.FStar_Syntax_Syntax.pos uu____3996);
              FStar_Pervasives_Native.None))
let binders_of_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders
  = fun e  -> FStar_TypeChecker_Env.all_binders e
let type_of_binder:
  'Auu____4006 .
    (FStar_Syntax_Syntax.bv,'Auu____4006) FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun b  -> match b with | (b1,uu____4022) -> b1.FStar_Syntax_Syntax.sort
let term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  FStar_Syntax_Util.term_eq
let fresh_binder:
  'Auu____4033 .
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.bv,'Auu____4033 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____4044 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t in
    (uu____4044, FStar_Pervasives_Native.None)
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  FStar_Syntax_Print.term_to_string