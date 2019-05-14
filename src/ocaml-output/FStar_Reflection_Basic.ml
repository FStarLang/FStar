open Prims
let (env_hook :
  FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (inspect_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Reflection_Data.aqualv) =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu____174)
        -> FStar_Reflection_Data.Q_Implicit
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
        FStar_Reflection_Data.Q_Meta t
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        FStar_Reflection_Data.Q_Explicit
    | FStar_Pervasives_Native.None  -> FStar_Reflection_Data.Q_Explicit
  
let (pack_aqual : FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.aqual)
  =
  fun aqv  ->
    match aqv with
    | FStar_Reflection_Data.Q_Explicit  -> FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Q_Implicit  ->
        FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit false)
    | FStar_Reflection_Data.Q_Meta t ->
        FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t)
  
let (inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv  ->
    let uu____213 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____213
  
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns  ->
    let lid = FStar_Parser_Const.p2l ns  in
    let fallback uu____257 =
      let quals =
        let uu____261 =
          FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid  in
        if uu____261
        then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
        else
          (let uu____268 =
             FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid  in
           if uu____268
           then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
           else
             (let uu____275 =
                FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid  in
              if uu____275
              then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
              else
                (let uu____282 =
                   FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid  in
                 if uu____282
                 then
                   FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
                 else FStar_Pervasives_Native.None)))
         in
      let uu____289 = FStar_Parser_Const.p2l ns  in
      FStar_Syntax_Syntax.lid_as_fv uu____289
        (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "999"))
        quals
       in
    let uu____299 = FStar_ST.op_Bang env_hook  in
    match uu____299 with
    | FStar_Pervasives_Native.None  -> fallback ()
    | FStar_Pervasives_Native.Some env ->
        let qninfo = FStar_TypeChecker_Env.lookup_qname env lid  in
        (match qninfo with
         | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,_us),_rng) ->
             let quals = FStar_Syntax_DsEnv.fv_qual_of_se se  in
             let uu____746 = FStar_Parser_Const.p2l ns  in
             FStar_Syntax_Syntax.lid_as_fv uu____746
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "999")) quals
         | uu____756 -> fallback ())
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____775::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____805 = init xs  in x :: uu____805
  
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____815) ->
        let uu____830 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____830
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____834) ->
        FStar_Reflection_Data.C_String s
    | FStar_Const.Const_range r -> FStar_Reflection_Data.C_Range r
    | FStar_Const.Const_reify  -> FStar_Reflection_Data.C_Reify
    | FStar_Const.Const_reflect l ->
        let uu____843 = FStar_Ident.path_of_lid l  in
        FStar_Reflection_Data.C_Reflect uu____843
    | uu____844 ->
        let uu____845 =
          let uu____847 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____847  in
        failwith uu____845
  
let rec (inspect_ln :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    let t3 = FStar_Syntax_Util.unlazy_emb t2  in
    match t3.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t4,uu____892) -> inspect_ln t4
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Reflection_Data.Tv_Var bv
    | FStar_Syntax_Syntax.Tm_bvar bv -> FStar_Reflection_Data.Tv_BVar bv
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect_ln: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1003 = last args  in
        (match uu____1003 with
         | (a,q) ->
             let q' = inspect_aqual q  in
             let uu____1047 =
               let uu____1056 =
                 let uu____1065 =
                   let uu____1070 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1070  in
                 uu____1065 FStar_Pervasives_Native.None
                   t3.FStar_Syntax_Syntax.pos
                  in
               (uu____1056, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____1047)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1091,uu____1092) ->
        failwith "inspect_ln: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs,t4,k) ->
        let body =
          match bs with
          | [] -> t4
          | bs1 ->
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_abs (bs1, t4, k))
                FStar_Pervasives_Native.None t4.FStar_Syntax_Syntax.pos
           in
        FStar_Reflection_Data.Tv_Abs (b, body)
    | FStar_Syntax_Syntax.Tm_type uu____1300 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect_ln: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____1339 ->
        let uu____1363 = FStar_Syntax_Util.arrow_one t3  in
        (match uu____1363 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
        FStar_Reflection_Data.Tv_Refine (bv, t4)
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____1439 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____1439
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
        let uu____1474 =
          let uu____1479 =
            let uu____1480 =
              FStar_Syntax_Unionfind.uvar_id
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            FStar_BigInt.of_int_fs uu____1480  in
          (uu____1479, (ctx_u, s))  in
        FStar_Reflection_Data.Tv_Uvar uu____1474
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____1567 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (false, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____1677 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (true, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____1800 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____1800
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____1833 =
                let uu____1843 =
                  FStar_List.map
                    (fun uu____1859  ->
                       match uu____1859 with
                       | (p1,uu____1868) -> inspect_pat p1) ps
                   in
                (fv, uu____1843)  in
              FStar_Reflection_Data.Pat_Cons uu____1833
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term (bv,t5) ->
              FStar_Reflection_Data.Pat_Dot_Term (bv, t5)
           in
        let brs1 =
          FStar_List.map
            (fun uu___0_1984  ->
               match uu___0_1984 with
               | (pat,uu____2018,t5) ->
                   let uu____2058 = inspect_pat pat  in (uu____2058, t5)) brs
           in
        FStar_Reflection_Data.Tv_Match (t4, brs1)
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Reflection_Data.Tv_Unknown
    | uu____2071 ->
        ((let uu____2073 =
            let uu____2079 =
              let uu____2081 = FStar_Syntax_Print.tag_of_term t3  in
              let uu____2083 = FStar_Syntax_Print.term_to_string t3  in
              FStar_Util.format2
                "inspect_ln: outside of expected syntax (%s, %s)\n"
                uu____2081 uu____2083
               in
            (FStar_Errors.Warning_CantInspect, uu____2079)  in
          FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____2073);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2102) ->
        FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____2139 =
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
           in
        if uu____2139
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2143)::(post,uu____2145)::uu____2146 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2225 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else
          (let uu____2243 =
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Tot_lid
              in
           if uu____2243
           then
             let maybe_dec =
               FStar_List.tryFind
                 (fun uu___1_2251  ->
                    match uu___1_2251 with
                    | FStar_Syntax_Syntax.DECREASES uu____2253 -> true
                    | uu____2261 -> false) ct.FStar_Syntax_Syntax.flags
                in
             let md =
               match maybe_dec with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   t) -> FStar_Pervasives_Native.Some t
               | uu____2291 -> failwith "impossible"  in
             FStar_Reflection_Data.C_Total
               ((ct.FStar_Syntax_Syntax.result_typ), md)
           else FStar_Reflection_Data.C_Unknown)
    | FStar_Syntax_Syntax.GTotal uu____2313 ->
        FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total (t,uu____2341) ->
        FStar_Syntax_Syntax.mk_Total t
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let ct =
          let uu____2391 =
            let uu____2406 = FStar_Syntax_Syntax.as_arg pre  in
            let uu____2419 =
              let uu____2434 = FStar_Syntax_Syntax.as_arg post  in
              [uu____2434]  in
            uu____2406 :: uu____2419  in
          {
            FStar_Syntax_Syntax.comp_univs = [];
            FStar_Syntax_Syntax.effect_name =
              FStar_Parser_Const.effect_Lemma_lid;
            FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
            FStar_Syntax_Syntax.effect_args = uu____2391;
            FStar_Syntax_Syntax.flags = []
          }  in
        FStar_Syntax_Syntax.mk_Comp ct
    | uu____2483 -> failwith "cannot pack a C_Unknown"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2496 =
          let uu____2508 = FStar_BigInt.string_of_big_int i  in
          (uu____2508, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____2496
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
    | FStar_Reflection_Data.C_Range r -> FStar_Const.Const_range r
    | FStar_Reflection_Data.C_Reify  -> FStar_Const.Const_reify
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____2528 = FStar_Ident.lid_of_path ns FStar_Range.dummyRange
           in
        FStar_Const.Const_reflect uu____2528
  
let (pack_ln : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv -> FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_BVar bv -> FStar_Syntax_Syntax.bv_to_tm bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = pack_aqual q  in FStar_Syntax_Util.mk_app l [(r, q')]
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) -> FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2711 =
          let uu____2718 =
            let uu____2719 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____2719  in
          FStar_Syntax_Syntax.mk uu____2718  in
        uu____2711 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,ctx_u_s) ->
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let ((false, [lb]), t2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let ((true, [lb]), t2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____2971 =
                let uu____2972 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____2972  in
              FStar_All.pipe_left wrap uu____2971
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2985 =
                let uu____2986 =
                  let uu____3006 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____3027 = pack_pat p1  in (uu____3027, false))
                      ps
                     in
                  (fv, uu____3006)  in
                FStar_Syntax_Syntax.Pat_cons uu____2986  in
              FStar_All.pipe_left wrap uu____2985
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv,t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1))
           in
        let brs1 =
          FStar_List.map
            (fun uu___2_3139  ->
               match uu___2_3139 with
               | (pat,t1) ->
                   let uu____3176 = pack_pat pat  in
                   (uu____3176, FStar_Pervasives_Native.None, t1)) brs
           in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs1))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             (e, ((FStar_Util.Inl t), tacopt), FStar_Pervasives_Native.None))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             (e, ((FStar_Util.Inr c), tacopt), FStar_Pervasives_Native.None))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
          FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (compare_bv :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv -> FStar_Order.order) =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv x y  in
      if n1 < (Prims.parse_int "0")
      then FStar_Order.Lt
      else
        if n1 = (Prims.parse_int "0") then FStar_Order.Eq else FStar_Order.Gt
  
let (is_free :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun x  -> fun t  -> FStar_Syntax_Util.is_free_in x t 
let (lookup_attr :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv Prims.list)
  =
  fun attr  ->
    fun env  ->
      let uu____3660 =
        let uu____3661 = FStar_Syntax_Subst.compress attr  in
        uu____3661.FStar_Syntax_Syntax.n  in
      match uu____3660 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let ses =
            let uu____3689 =
              let uu____3691 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_Ident.text_of_lid uu____3691  in
            FStar_TypeChecker_Env.lookup_attr env uu____3689  in
          FStar_List.concatMap
            (fun se  ->
               let uu____3716 = FStar_Syntax_Util.lid_of_sigelt se  in
               match uu____3716 with
               | FStar_Pervasives_Native.None  -> []
               | FStar_Pervasives_Native.Some l ->
                   let uu____3744 =
                     FStar_Syntax_Syntax.lid_as_fv l
                       (FStar_Syntax_Syntax.Delta_constant_at_level
                          (Prims.parse_int "999"))
                       FStar_Pervasives_Native.None
                      in
                   [uu____3744]) ses
      | uu____3758 -> []
  
let (lookup_typ :
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ns  ->
      let lid = FStar_Parser_Const.p2l ns  in
      FStar_TypeChecker_Env.lookup_sigelt env lid
  
let (sigelt_attrs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.attribute Prims.list) =
  fun se  -> se.FStar_Syntax_Syntax.sigattrs 
let (set_sigelt_attrs :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun attrs  ->
    fun se  ->
      let uu___363_3981 = se  in
      {
        FStar_Syntax_Syntax.sigel = (uu___363_3981.FStar_Syntax_Syntax.sigel);
        FStar_Syntax_Syntax.sigrng =
          (uu___363_3981.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals =
          (uu___363_3981.FStar_Syntax_Syntax.sigquals);
        FStar_Syntax_Syntax.sigmeta =
          (uu___363_3981.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs = attrs
      }
  
let (inspect_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_Data.sigelt_view) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let ((r,lb::[]),uu____4010) ->
        let fv =
          match lb.FStar_Syntax_Syntax.lbname with
          | FStar_Util.Inr fv -> fv
          | FStar_Util.Inl uu____4077 ->
              failwith "impossible: global Sig_let has bv"
           in
        let uu____4095 =
          FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs
           in
        (match uu____4095 with
         | (s,us) ->
             let typ =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbtyp  in
             let def =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbdef  in
             FStar_Reflection_Data.Sg_Let
               (r, fv, (lb.FStar_Syntax_Syntax.lbunivs),
                 (lb.FStar_Syntax_Syntax.lbtyp),
                 (lb.FStar_Syntax_Syntax.lbdef)))
    | FStar_Syntax_Syntax.Sig_inductive_typ (lid,us,bs,ty,uu____4158,c_lids)
        ->
        let nm = FStar_Ident.path_of_lid lid  in
        let uu____4201 = FStar_Syntax_Subst.univ_var_opening us  in
        (match uu____4201 with
         | (s,us1) ->
             let bs1 = FStar_Syntax_Subst.subst_binders s bs  in
             let ty1 = FStar_Syntax_Subst.subst s ty  in
             let uu____4236 =
               let uu____4259 = FStar_List.map FStar_Ident.path_of_lid c_lids
                  in
               (nm, us1, bs1, ty1, uu____4259)  in
             FStar_Reflection_Data.Sg_Inductive uu____4236)
    | FStar_Syntax_Syntax.Sig_datacon (lid,us,ty,uu____4281,n1,uu____4283) ->
        let uu____4322 = FStar_Syntax_Subst.univ_var_opening us  in
        (match uu____4322 with
         | (s,us1) ->
             let ty1 = FStar_Syntax_Subst.subst s ty  in
             let uu____4356 =
               let uu____4365 = FStar_Ident.path_of_lid lid  in
               (uu____4365, ty1)  in
             FStar_Reflection_Data.Sg_Constructor uu____4356)
    | uu____4370 -> FStar_Reflection_Data.Unk
  
let (pack_sigelt :
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.sigelt) =
  fun sv  ->
    match sv with
    | FStar_Reflection_Data.Sg_Let (r,fv,univs1,typ,def) ->
        let s = FStar_Syntax_Subst.univ_var_closing univs1  in
        let typ1 = FStar_Syntax_Subst.subst s typ  in
        let def1 = FStar_Syntax_Subst.subst s def  in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inr fv) univs1 typ1
            FStar_Parser_Const.effect_Tot_lid def1 []
            def1.FStar_Syntax_Syntax.pos
           in
        let uu____4474 =
          let uu____4475 =
            let uu____4486 =
              let uu____4493 = FStar_Syntax_Syntax.lid_of_fv fv  in
              [uu____4493]  in
            ((r, [lb]), uu____4486)  in
          FStar_Syntax_Syntax.Sig_let uu____4475  in
        FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt uu____4474
    | FStar_Reflection_Data.Sg_Constructor uu____4545 ->
        failwith "packing Sg_Constructor, sorry"
    | FStar_Reflection_Data.Sg_Inductive uu____4560 ->
        failwith "packing Sg_Inductive, sorry"
    | FStar_Reflection_Data.Unk  -> failwith "packing Unk, sorry"
  
let (inspect_bv : FStar_Syntax_Syntax.bv -> FStar_Reflection_Data.bv_view) =
  fun bv  ->
    let uu____4617 =
      FStar_Ident.string_of_ident bv.FStar_Syntax_Syntax.ppname  in
    let uu____4619 = FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index  in
    {
      FStar_Reflection_Data.bv_ppname = uu____4617;
      FStar_Reflection_Data.bv_index = uu____4619;
      FStar_Reflection_Data.bv_sort = (bv.FStar_Syntax_Syntax.sort)
    }
  
let (pack_bv : FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.bv) =
  fun bvv  ->
    let uu____4642 =
      FStar_Ident.mk_ident
        ((bvv.FStar_Reflection_Data.bv_ppname), FStar_Range.dummyRange)
       in
    let uu____4648 =
      FStar_BigInt.to_int_fs bvv.FStar_Reflection_Data.bv_index  in
    {
      FStar_Syntax_Syntax.ppname = uu____4642;
      FStar_Syntax_Syntax.index = uu____4648;
      FStar_Syntax_Syntax.sort = (bvv.FStar_Reflection_Data.bv_sort)
    }
  
let (inspect_binder :
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.bv * FStar_Reflection_Data.aqualv))
  =
  fun b  ->
    let uu____4674 = b  in
    match uu____4674 with
    | (bv,aq) -> let uu____4700 = inspect_aqual aq  in (bv, uu____4700)
  
let (pack_binder :
  FStar_Syntax_Syntax.bv ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.binder)
  =
  fun bv  -> fun aqv  -> let uu____4727 = pack_aqual aqv  in (bv, uu____4727) 
let (moduleof : FStar_TypeChecker_Env.env -> Prims.string Prims.list) =
  fun e  -> FStar_Ident.path_of_lid e.FStar_TypeChecker_Env.curmodule 
let (env_open_modules :
  FStar_TypeChecker_Env.env -> FStar_Reflection_Data.name Prims.list) =
  fun e  ->
    let uu____4975 =
      FStar_Syntax_DsEnv.open_modules e.FStar_TypeChecker_Env.dsenv  in
    FStar_List.map
      (fun uu____5017  ->
         match uu____5017 with
         | (l,m) ->
             let uu____5063 = FStar_Ident.ids_of_lid l  in
             FStar_List.map FStar_Ident.text_of_id uu____5063) uu____4975
  
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____5213 = FStar_Syntax_Util.un_uinst t1  in
      let uu____5222 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____5213 uu____5222
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 
let (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  -> FStar_Syntax_Print.comp_to_string c 