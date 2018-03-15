open Prims
let (inspect_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Reflection_Data.aqualv) =
  fun aq ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu____4) ->
        FStar_Reflection_Data.Q_Implicit
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) ->
        FStar_Reflection_Data.Q_Explicit
    | FStar_Pervasives_Native.None -> FStar_Reflection_Data.Q_Explicit
let (pack_aqual : FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.aqual)
  =
  fun aqv ->
    match aqv with
    | FStar_Reflection_Data.Q_Explicit -> FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Q_Implicit ->
        FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit false)
let (inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv ->
    let uu____15 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____15
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns ->
    let lid = FStar_Parser_Const.p2l ns in
    let attr =
      if FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid
      then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
      else
        if FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid
        then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
        else
          if FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid
          then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
          else
            if FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
            else FStar_Pervasives_Native.None in
    let uu____39 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____39
      (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "999"))
      attr
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____53::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____78 = init xs in x :: uu____78
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c ->
    match c with
    | FStar_Const.Const_unit -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s, uu____85) ->
        let uu____98 = FStar_BigInt.big_int_of_string s in
        FStar_Reflection_Data.C_Int uu____98
    | FStar_Const.Const_bool (true) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s, uu____100) ->
        FStar_Reflection_Data.C_String s
    | uu____101 ->
        let uu____102 =
          let uu____103 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____103 in
        failwith uu____102
let rec (inspect_ln :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let t2 = FStar_Syntax_Util.un_uinst t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3, uu____110) -> inspect_ln t3
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Reflection_Data.Tv_Var bv
    | FStar_Syntax_Syntax.Tm_bvar bv -> FStar_Reflection_Data.Tv_BVar bv
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1, []) ->
        failwith "inspect_ln: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1, args) ->
        let uu____159 = last args in
        (match uu____159 with
         | (a, q) ->
             let q' = inspect_aqual q in
             let uu____179 =
               let uu____184 =
                 let uu____187 =
                   let uu____188 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____188 in
                 uu____187 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos in
               (uu____184, (a, q')) in
             FStar_Reflection_Data.Tv_App uu____179)
    | FStar_Syntax_Syntax.Tm_abs ([], uu____207, uu____208) ->
        failwith "inspect_ln: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs, t3, k) ->
        let body =
          match bs with
          | [] -> t3
          | bs1 ->
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_abs (bs1, t3, k))
                FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos in
        FStar_Reflection_Data.Tv_Abs (b, body)
    | FStar_Syntax_Syntax.Tm_type uu____291 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([], k) ->
        failwith "inspect_ln: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____307 ->
        let uu____320 = FStar_Syntax_Util.arrow_one t2 in
        (match uu____320 with
         | FStar_Pervasives_Native.Some (b, c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv, t3) ->
        FStar_Reflection_Data.Tv_Refine (bv, t3)
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____346 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____346
    | FStar_Syntax_Syntax.Tm_uvar (u, t3) ->
        let uu____373 =
          let uu____378 =
            let uu____379 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_BigInt.of_int_fs uu____379 in
          (uu____378, t3) in
        FStar_Reflection_Data.Tv_Uvar uu____373
    | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____399 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (false, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_let ((true, lb::[]), t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____422 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (true, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_match (t3, brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____475 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____475
          | FStar_Syntax_Syntax.Pat_cons (fv, ps) ->
              let uu____494 =
                let uu____501 =
                  FStar_List.map
                    (fun uu____513 ->
                       match uu____513 with
                       | (p1, uu____521) -> inspect_pat p1) ps in
                (fv, uu____501) in
              FStar_Reflection_Data.Pat_Cons uu____494
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term (bv, t4) ->
              FStar_Reflection_Data.Pat_Dot_Term (bv, t4) in
        let brs1 =
          FStar_List.map
            (fun uu___54_572 ->
               match uu___54_572 with
               | (pat, uu____594, t4) ->
                   let uu____612 = inspect_pat pat in (uu____612, t4)) brs in
        FStar_Reflection_Data.Tv_Match (t3, brs1)
    | FStar_Syntax_Syntax.Tm_unknown -> FStar_Reflection_Data.Tv_Unknown
    | uu____625 ->
        ((let uu____627 =
            let uu____632 =
              let uu____633 = FStar_Syntax_Print.tag_of_term t2 in
              let uu____634 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Util.format2
                "inspect_ln: outside of expected syntax (%s, %s)\n" uu____633
                uu____634 in
            (FStar_Errors.Warning_CantInspect, uu____632) in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____627);
         FStar_Reflection_Data.Tv_Unknown)
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uu____639) ->
        FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre, uu____654)::(post, uu____656)::uu____657 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____690 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else
          if
            FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
              FStar_Parser_Const.effect_Tot_lid
          then
            (let maybe_dec =
               FStar_List.tryFind
                 (fun uu___55_705 ->
                    match uu___55_705 with
                    | FStar_Syntax_Syntax.DECREASES uu____706 -> true
                    | uu____709 -> false) ct.FStar_Syntax_Syntax.flags in
             let md =
               match maybe_dec with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   t) -> FStar_Pervasives_Native.Some t
               | uu____726 -> failwith "impossible" in
             FStar_Reflection_Data.C_Total
               ((ct.FStar_Syntax_Syntax.result_typ), md))
          else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____740 -> FStar_Reflection_Data.C_Unknown
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv ->
    match cv with
    | FStar_Reflection_Data.C_Total (t, uu____753) ->
        FStar_Syntax_Syntax.mk_Total t
    | uu____758 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c ->
    match c with
    | FStar_Reflection_Data.C_Unit -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____763 =
          let uu____774 = FStar_BigInt.string_of_big_int i in
          (uu____774, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____763
    | FStar_Reflection_Data.C_True -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
let (pack_ln : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv -> FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_BVar bv -> FStar_Syntax_Syntax.bv_to_tm bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
        let q' = pack_aqual q in FStar_Syntax_Util.mk_app l [(r, q')]
    | FStar_Reflection_Data.Tv_Abs (b, t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b, c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv, t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____815 =
          let uu____818 =
            let uu____819 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____819 in
          FStar_Syntax_Syntax.mk uu____818 in
        uu____815 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u, t) ->
        let uu____825 = FStar_BigInt.to_int_fs u in
        FStar_Syntax_Util.uvar_from_id uu____825 t
    | FStar_Reflection_Data.Tv_Let (false, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let ((false, [lb]), t2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (true, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let ((true, [lb]), t2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t, brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____871 =
                let uu____872 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____872 in
              FStar_All.pipe_left wrap uu____871
          | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
              let uu____881 =
                let uu____882 =
                  let uu____895 =
                    FStar_List.map
                      (fun p1 ->
                         let uu____909 = pack_pat p1 in (uu____909, false))
                      ps in
                  (fv, uu____895) in
                FStar_Syntax_Syntax.Pat_cons uu____882 in
              FStar_All.pipe_left wrap uu____881
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv, t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1)) in
        let brs1 =
          FStar_List.map
            (fun uu___56_959 ->
               match uu___56_959 with
               | (pat, t1) ->
                   let uu____976 = pack_pat pat in
                   (uu____976, FStar_Pervasives_Native.None, t1)) brs in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs1))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             (e, ((FStar_Util.Inl t), tacopt), FStar_Pervasives_Native.None))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             (e, ((FStar_Util.Inr c), tacopt), FStar_Pervasives_Native.None))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown ->
        FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
          FStar_Pervasives_Native.None FStar_Range.dummyRange
let (compare_bv :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv -> FStar_Order.order) =
  fun x ->
    fun y ->
      let n1 = FStar_Syntax_Syntax.order_bv x y in
      if n1 < (Prims.parse_int "0")
      then FStar_Order.Lt
      else
        if n1 = (Prims.parse_int "0") then FStar_Order.Eq else FStar_Order.Gt
let (is_free :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun x -> fun t -> FStar_Syntax_Util.is_free_in x t
let (lookup_typ :
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ns ->
      let lid = FStar_Parser_Const.p2l ns in
      let uu____1087 = FStar_TypeChecker_Env.lookup_qname env lid in
      match uu____1087 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____1108, rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) ->
          FStar_Pervasives_Native.Some se
let (inspect_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_Data.sigelt_view) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let ((r, lb::[]), uu____1210) ->
        let fv =
          match lb.FStar_Syntax_Syntax.lbname with
          | FStar_Util.Inr fv -> fv
          | FStar_Util.Inl uu____1225 -> failwith "global Sig_let has bv" in
        FStar_Reflection_Data.Sg_Let
          (r, fv, (lb.FStar_Syntax_Syntax.lbtyp),
            (lb.FStar_Syntax_Syntax.lbdef))
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid, us, bs, t, uu____1234, c_lids) ->
        let nm = FStar_Ident.path_of_lid lid in
        let uu____1247 =
          let uu____1260 = FStar_List.map FStar_Ident.path_of_lid c_lids in
          (nm, bs, t, uu____1260) in
        FStar_Reflection_Data.Sg_Inductive uu____1247
    | FStar_Syntax_Syntax.Sig_datacon
        (lid, us, t, uu____1276, n1, uu____1278) ->
        let uu____1283 =
          let uu____1288 = FStar_Ident.path_of_lid lid in (uu____1288, t) in
        FStar_Reflection_Data.Sg_Constructor uu____1283
    | uu____1293 -> FStar_Reflection_Data.Unk
let (pack_sigelt :
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.sigelt) =
  fun sv ->
    match sv with
    | FStar_Reflection_Data.Sg_Let (r, fv, ty, def) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inr fv) [] ty
            FStar_Parser_Const.effect_Tot_lid def []
            def.FStar_Syntax_Syntax.pos in
        let uu____1304 =
          let uu____1305 =
            let uu____1312 =
              let uu____1315 = FStar_Syntax_Syntax.lid_of_fv fv in
              [uu____1315] in
            ((r, [lb]), uu____1312) in
          FStar_Syntax_Syntax.Sig_let uu____1305 in
        FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt uu____1304
    | FStar_Reflection_Data.Sg_Constructor uu____1326 ->
        failwith "packing Sg_Constructor, sorry"
    | FStar_Reflection_Data.Sg_Inductive uu____1331 ->
        failwith "packing Sg_Inductive, sorry"
    | FStar_Reflection_Data.Unk -> failwith "packing Unk, sorry"
let (inspect_bv : FStar_Syntax_Syntax.bv -> FStar_Reflection_Data.bv_view) =
  fun bv ->
    let uu____1347 = FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index in
    {
      FStar_Reflection_Data.bv_ppname =
        (FStar_Ident.string_of_ident bv.FStar_Syntax_Syntax.ppname);
      FStar_Reflection_Data.bv_index = uu____1347;
      FStar_Reflection_Data.bv_sort = (bv.FStar_Syntax_Syntax.sort)
    }
let (pack_bv : FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.bv) =
  fun bvv ->
    let uu____1351 =
      FStar_BigInt.to_int_fs bvv.FStar_Reflection_Data.bv_index in
    {
      FStar_Syntax_Syntax.ppname =
        (FStar_Ident.mk_ident
           ((bvv.FStar_Reflection_Data.bv_ppname), FStar_Range.dummyRange));
      FStar_Syntax_Syntax.index = uu____1351;
      FStar_Syntax_Syntax.sort = (bvv.FStar_Reflection_Data.bv_sort)
    }
let (inspect_binder :
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.bv, FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2)
  =
  fun b ->
    let uu____1363 = b in
    match uu____1363 with
    | (bv, aq) -> let uu____1370 = inspect_aqual aq in (bv, uu____1370)
let (pack_binder :
  FStar_Syntax_Syntax.bv ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.binder)
  = fun bv -> fun aqv -> let uu____1377 = pack_aqual aqv in (bv, uu____1377)
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e -> FStar_TypeChecker_Env.all_binders e
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      let uu____1387 = FStar_Syntax_Util.un_uinst t1 in
      let uu____1388 = FStar_Syntax_Util.un_uinst t2 in
      FStar_Syntax_Util.term_eq uu____1387 uu____1388
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t -> FStar_Syntax_Print.term_to_string t