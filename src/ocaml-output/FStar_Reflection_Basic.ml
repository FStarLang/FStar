open Prims
let (env_hook :
  FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (inspect_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Reflection_Data.aqualv) =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu____34) ->
        FStar_Reflection_Data.Q_Implicit
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
    let uu____53 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____53
  
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns  ->
    let lid = FStar_Parser_Const.p2l ns  in
    let fallback uu____69 =
      let quals =
        let uu____73 = FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid
           in
        if uu____73
        then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
        else
          (let uu____77 =
             FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid  in
           if uu____77
           then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
           else
             (let uu____81 =
                FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid  in
              if uu____81
              then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
              else
                (let uu____85 =
                   FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid  in
                 if uu____85
                 then
                   FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
                 else FStar_Pervasives_Native.None)))
         in
      let uu____89 = FStar_Parser_Const.p2l ns  in
      FStar_Syntax_Syntax.lid_as_fv uu____89
        (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "999"))
        quals
       in
    let uu____90 = FStar_ST.op_Bang env_hook  in
    match uu____90 with
    | FStar_Pervasives_Native.None  -> fallback ()
    | FStar_Pervasives_Native.Some env ->
        let qninfo = FStar_TypeChecker_Env.lookup_qname env lid  in
        (match qninfo with
         | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,_us),_rng) ->
             let quals = FStar_Syntax_DsEnv.fv_qual_of_se se  in
             let uu____192 = FStar_Parser_Const.p2l ns  in
             FStar_Syntax_Syntax.lid_as_fv uu____192
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "999")) quals
         | uu____193 -> fallback ())
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____210::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____238 = init xs  in x :: uu____238
  
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____247) ->
        let uu____260 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____260
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____262) ->
        FStar_Reflection_Data.C_String s
    | uu____263 ->
        let uu____264 =
          let uu____265 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____265  in
        failwith uu____264
  
let rec (inspect_ln :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____274) -> inspect_ln t3
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Reflection_Data.Tv_Var bv
    | FStar_Syntax_Syntax.Tm_bvar bv -> FStar_Reflection_Data.Tv_BVar bv
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect_ln: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____331 = last args  in
        (match uu____331 with
         | (a,q) ->
             let q' = inspect_aqual q  in
             let uu____359 =
               let uu____364 =
                 let uu____365 =
                   let uu____370 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____370  in
                 uu____365 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos
                  in
               (uu____364, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____359)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____381,uu____382) ->
        failwith "inspect_ln: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs,t3,k) ->
        let body =
          match bs with
          | [] -> t3
          | bs1 ->
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_abs (bs1, t3, k))
                FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
           in
        FStar_Reflection_Data.Tv_Abs (b, body)
    | FStar_Syntax_Syntax.Tm_type uu____473 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect_ln: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____493 ->
        let uu____508 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____508 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        FStar_Reflection_Data.Tv_Refine (bv, t3)
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____564 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____564
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
        let uu____583 =
          let uu____588 =
            let uu____589 =
              FStar_Syntax_Unionfind.uvar_id
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            FStar_BigInt.of_int_fs uu____589  in
          (uu____588, (ctx_u, s))  in
        FStar_Reflection_Data.Tv_Uvar uu____583
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____615 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (false, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____634 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (true, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____685 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____685
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____704 =
                let uu____711 =
                  FStar_List.map
                    (fun uu____723  ->
                       match uu____723 with
                       | (p1,uu____731) -> inspect_pat p1) ps
                   in
                (fv, uu____711)  in
              FStar_Reflection_Data.Pat_Cons uu____704
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term (bv,t4) ->
              FStar_Reflection_Data.Pat_Dot_Term (bv, t4)
           in
        let brs1 =
          FStar_List.map
            (fun uu___224_780  ->
               match uu___224_780 with
               | (pat,uu____802,t4) ->
                   let uu____820 = inspect_pat pat  in (uu____820, t4)) brs
           in
        FStar_Reflection_Data.Tv_Match (t3, brs1)
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Reflection_Data.Tv_Unknown
    | uu____825 ->
        ((let uu____827 =
            let uu____832 =
              let uu____833 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____834 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect_ln: outside of expected syntax (%s, %s)\n" uu____833
                uu____834
               in
            (FStar_Errors.Warning_CantInspect, uu____832)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____827);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____841) ->
        FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____853 =
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
           in
        if uu____853
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____855)::(post,uu____857)::uu____858 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____901 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else
          (let uu____913 =
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Tot_lid
              in
           if uu____913
           then
             let maybe_dec =
               FStar_List.tryFind
                 (fun uu___225_919  ->
                    match uu___225_919 with
                    | FStar_Syntax_Syntax.DECREASES uu____920 -> true
                    | uu____923 -> false) ct.FStar_Syntax_Syntax.flags
                in
             let md =
               match maybe_dec with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   t) -> FStar_Pervasives_Native.Some t
               | uu____932 -> failwith "impossible"  in
             FStar_Reflection_Data.C_Total
               ((ct.FStar_Syntax_Syntax.result_typ), md)
           else FStar_Reflection_Data.C_Unknown)
    | FStar_Syntax_Syntax.GTotal uu____940 -> FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total (t,uu____955) ->
        FStar_Syntax_Syntax.mk_Total t
    | uu____968 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____975 =
          let uu____986 = FStar_BigInt.string_of_big_int i  in
          (uu____986, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____975
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
  
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
        let uu____1111 =
          let uu____1118 =
            let uu____1119 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____1119  in
          FStar_Syntax_Syntax.mk uu____1118  in
        uu____1111 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
              let uu____1234 =
                let uu____1235 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____1235  in
              FStar_All.pipe_left wrap uu____1234
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____1242 =
                let uu____1243 =
                  let uu____1256 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____1272 = pack_pat p1  in (uu____1272, false))
                      ps
                     in
                  (fv, uu____1256)  in
                FStar_Syntax_Syntax.Pat_cons uu____1243  in
              FStar_All.pipe_left wrap uu____1242
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
            (fun uu___226_1328  ->
               match uu___226_1328 with
               | (pat,t1) ->
                   let uu____1353 = pack_pat pat  in
                   (uu____1353, FStar_Pervasives_Native.None, t1)) brs
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
      let uu____1527 =
        let uu____1528 = FStar_Syntax_Subst.compress attr  in
        uu____1528.FStar_Syntax_Syntax.n  in
      match uu____1527 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let ses =
            let uu____1537 =
              let uu____1538 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_Ident.text_of_lid uu____1538  in
            FStar_TypeChecker_Env.lookup_attr env uu____1537  in
          FStar_List.concatMap
            (fun se  ->
               let uu____1542 = FStar_Syntax_Util.lid_of_sigelt se  in
               match uu____1542 with
               | FStar_Pervasives_Native.None  -> []
               | FStar_Pervasives_Native.Some l ->
                   let uu____1548 =
                     FStar_Syntax_Syntax.lid_as_fv l
                       (FStar_Syntax_Syntax.Delta_constant_at_level
                          (Prims.parse_int "999"))
                       FStar_Pervasives_Native.None
                      in
                   [uu____1548]) ses
      | uu____1549 -> []
  
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
      let uu___227_1592 = se  in
      {
        FStar_Syntax_Syntax.sigel = (uu___227_1592.FStar_Syntax_Syntax.sigel);
        FStar_Syntax_Syntax.sigrng =
          (uu___227_1592.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals =
          (uu___227_1592.FStar_Syntax_Syntax.sigquals);
        FStar_Syntax_Syntax.sigmeta =
          (uu___227_1592.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs = attrs
      }
  
let (inspect_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_Data.sigelt_view) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let ((r,lb::[]),uu____1600) ->
        let fv =
          match lb.FStar_Syntax_Syntax.lbname with
          | FStar_Util.Inr fv -> fv
          | FStar_Util.Inl uu____1615 ->
              failwith "impossible: global Sig_let has bv"
           in
        let uu____1616 =
          FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs
           in
        (match uu____1616 with
         | (s,us) ->
             let typ =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbtyp  in
             let def =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbdef  in
             FStar_Reflection_Data.Sg_Let
               (r, fv, (lb.FStar_Syntax_Syntax.lbunivs),
                 (lb.FStar_Syntax_Syntax.lbtyp),
                 (lb.FStar_Syntax_Syntax.lbdef)))
    | FStar_Syntax_Syntax.Sig_inductive_typ (lid,us,bs,ty,uu____1643,c_lids)
        ->
        let nm = FStar_Ident.path_of_lid lid  in
        let uu____1678 = FStar_Syntax_Subst.univ_var_opening us  in
        (match uu____1678 with
         | (s,us1) ->
             let bs1 = FStar_Syntax_Subst.subst_binders s bs  in
             let ty1 = FStar_Syntax_Subst.subst s ty  in
             let uu____1699 =
               let uu____1716 = FStar_List.map FStar_Ident.path_of_lid c_lids
                  in
               (nm, us1, bs1, ty1, uu____1716)  in
             FStar_Reflection_Data.Sg_Inductive uu____1699)
    | FStar_Syntax_Syntax.Sig_datacon (lid,us,ty,uu____1728,n1,uu____1730) ->
        let uu____1743 = FStar_Syntax_Subst.univ_var_opening us  in
        (match uu____1743 with
         | (s,us1) ->
             let ty1 = FStar_Syntax_Subst.subst s ty  in
             let uu____1763 =
               let uu____1768 = FStar_Ident.path_of_lid lid  in
               (uu____1768, ty1)  in
             FStar_Reflection_Data.Sg_Constructor uu____1763)
    | uu____1769 -> FStar_Reflection_Data.Unk
  
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
        let uu____1800 =
          let uu____1801 =
            let uu____1808 =
              let uu____1811 = FStar_Syntax_Syntax.lid_of_fv fv  in
              [uu____1811]  in
            ((r, [lb]), uu____1808)  in
          FStar_Syntax_Syntax.Sig_let uu____1801  in
        FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt uu____1800
    | FStar_Reflection_Data.Sg_Constructor uu____1816 ->
        failwith "packing Sg_Constructor, sorry"
    | FStar_Reflection_Data.Sg_Inductive uu____1821 ->
        failwith "packing Sg_Inductive, sorry"
    | FStar_Reflection_Data.Unk  -> failwith "packing Unk, sorry"
  
let (inspect_bv : FStar_Syntax_Syntax.bv -> FStar_Reflection_Data.bv_view) =
  fun bv  ->
    let uu____1843 =
      FStar_Ident.string_of_ident bv.FStar_Syntax_Syntax.ppname  in
    let uu____1844 = FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index  in
    {
      FStar_Reflection_Data.bv_ppname = uu____1843;
      FStar_Reflection_Data.bv_index = uu____1844;
      FStar_Reflection_Data.bv_sort = (bv.FStar_Syntax_Syntax.sort)
    }
  
let (pack_bv : FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.bv) =
  fun bvv  ->
    let uu____1850 =
      FStar_Ident.mk_ident
        ((bvv.FStar_Reflection_Data.bv_ppname), FStar_Range.dummyRange)
       in
    let uu____1851 =
      FStar_BigInt.to_int_fs bvv.FStar_Reflection_Data.bv_index  in
    {
      FStar_Syntax_Syntax.ppname = uu____1850;
      FStar_Syntax_Syntax.index = uu____1851;
      FStar_Syntax_Syntax.sort = (bvv.FStar_Reflection_Data.bv_sort)
    }
  
let (inspect_binder :
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.bv,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2)
  =
  fun b  ->
    let uu____1865 = b  in
    match uu____1865 with
    | (bv,aq) -> let uu____1876 = inspect_aqual aq  in (bv, uu____1876)
  
let (pack_binder :
  FStar_Syntax_Syntax.bv ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.binder)
  =
  fun bv  -> fun aqv  -> let uu____1887 = pack_aqual aqv  in (bv, uu____1887) 
let (moduleof : FStar_TypeChecker_Env.env -> Prims.string Prims.list) =
  fun e  -> FStar_Ident.path_of_lid e.FStar_TypeChecker_Env.curmodule 
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____1916 = FStar_Syntax_Util.un_uinst t1  in
      let uu____1917 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____1916 uu____1917
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 