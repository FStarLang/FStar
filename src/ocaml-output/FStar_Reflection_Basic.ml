open Prims
let (inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv  ->
    let uu____8 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____8
  
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns  ->
    let uu____16 = FStar_Parser_Const.p2l ns  in
    FStar_Syntax_Syntax.lid_as_fv uu____16
      (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "999"))
      FStar_Pervasives_Native.None
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____30::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____55 = init xs  in x :: uu____55
  
let (inspect_bv : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b) 
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____65) ->
        let uu____78 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____78
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____80) ->
        FStar_Reflection_Data.C_String s
    | uu____81 ->
        let uu____82 =
          let uu____83 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____83  in
        failwith uu____82
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____90) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____96 = FStar_Syntax_Syntax.mk_binder bv  in
        FStar_Reflection_Data.Tv_Var uu____96
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____139 = last args  in
        (match uu____139 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____159) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit
                in
             let uu____160 =
               let uu____165 =
                 let uu____168 =
                   let uu____169 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____169  in
                 uu____168 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos
                  in
               (uu____165, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____160)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____188,uu____189) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____231 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____231 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____258 =
                    let uu____263 = FStar_Syntax_Util.abs bs2 t4 k  in
                    (b, uu____263)  in
                  FStar_Reflection_Data.Tv_Abs uu____258))
    | FStar_Syntax_Syntax.Tm_type uu____268 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____284 ->
        let uu____297 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____297 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____321 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____321 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____350 -> failwith "impossible"  in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____360 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____360
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____387 =
          let uu____392 =
            let uu____393 = FStar_Syntax_Unionfind.uvar_id u  in
            FStar_BigInt.of_int_fs uu____393  in
          (uu____392, t3)  in
        FStar_Reflection_Data.Tv_Uvar uu____387
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____413 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____416 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____416 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____445 ->
                          failwith
                            "impossible: open_term returned different amount of binders"
                       in
                    FStar_Reflection_Data.Tv_Let
                      (false, b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____473 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____475 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____475 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____489 ->
                              FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              let uu____491 =
                                let uu____500 =
                                  FStar_Syntax_Syntax.mk_binder bv1  in
                                (true, uu____500,
                                  (lb1.FStar_Syntax_Syntax.lbdef), t22)
                                 in
                              FStar_Reflection_Data.Tv_Let uu____491)
                     | uu____503 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____553 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____553
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____572 =
                let uu____579 =
                  FStar_List.map
                    (fun uu____591  ->
                       match uu____591 with
                       | (p1,uu____599) -> inspect_pat p1) ps
                   in
                (fv, uu____579)  in
              FStar_Reflection_Data.Pat_Cons uu____572
          | FStar_Syntax_Syntax.Pat_var bv ->
              let uu____607 = FStar_Syntax_Syntax.mk_binder bv  in
              FStar_Reflection_Data.Pat_Var uu____607
          | FStar_Syntax_Syntax.Pat_wild bv ->
              let uu____609 = FStar_Syntax_Syntax.mk_binder bv  in
              FStar_Reflection_Data.Pat_Wild uu____609
          | FStar_Syntax_Syntax.Pat_dot_term uu____610 ->
              failwith "NYI: Pat_dot_term"
           in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
        let brs2 =
          FStar_List.map
            (fun uu___53_654  ->
               match uu___53_654 with
               | (pat,uu____676,t4) ->
                   let uu____694 = inspect_pat pat  in (uu____694, t4)) brs1
           in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____707 ->
        ((let uu____709 =
            let uu____714 =
              let uu____715 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____716 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____715
                uu____716
               in
            (FStar_Errors.Warning_CantInspect, uu____714)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____709);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____721) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____732)::(post,uu____734)::uu____735 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____768 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____778 -> FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____791 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____796 =
          let uu____807 = FStar_BigInt.string_of_big_int i  in
          (uu____807, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____796
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____823) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____832 =
               let uu____841 = FStar_Syntax_Syntax.as_arg r  in [uu____841]
                in
             FStar_Syntax_Util.mk_app l uu____832
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____842 =
               let uu____851 = FStar_Syntax_Syntax.iarg r  in [uu____851]  in
             FStar_Syntax_Util.mk_app l uu____842)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____857),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____864 =
          let uu____867 =
            let uu____868 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____868  in
          FStar_Syntax_Syntax.mk uu____867  in
        uu____864 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____874 = FStar_BigInt.to_int_fs u  in
        FStar_Syntax_Util.uvar_from_id uu____874 t
    | FStar_Reflection_Data.Tv_Let (false ,b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b  in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____882 =
          let uu____885 =
            let uu____886 =
              let uu____899 = FStar_Syntax_Subst.close [b] t2  in
              ((false, [lb]), uu____899)  in
            FStar_Syntax_Syntax.Tm_let uu____886  in
          FStar_Syntax_Syntax.mk uu____885  in
        uu____882 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (true ,b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b  in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____918 = FStar_Syntax_Subst.open_let_rec [lb] t2  in
        (match uu____918 with
         | (lbs_open,body_open) ->
             let uu____931 = FStar_Syntax_Subst.close_let_rec [lb] body_open
                in
             (match uu____931 with
              | (lbs,body) ->
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange))
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____969 =
                let uu____970 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____970  in
              FStar_All.pipe_left wrap uu____969
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____979 =
                let uu____980 =
                  let uu____993 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____1007 = pack_pat p1  in (uu____1007, false))
                      ps
                     in
                  (fv, uu____993)  in
                FStar_Syntax_Syntax.Pat_cons uu____980  in
              FStar_All.pipe_left wrap uu____979
          | FStar_Reflection_Data.Pat_Var (bv,uu____1017) ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild (bv,uu____1021) ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
           in
        let brs1 =
          FStar_List.map
            (fun uu___54_1055  ->
               match uu___54_1055 with
               | (pat,t1) ->
                   let uu____1072 = pack_pat pat  in
                   (uu____1072, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        failwith "pack: unexpected term view"
  
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
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ns  ->
      let lid = FStar_Parser_Const.p2l ns  in
      let uu____1114 = FStar_TypeChecker_Env.lookup_qname env lid  in
      match uu____1114 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____1135,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (inspect_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_Data.sigelt_view) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let ((r,lb::[]),uu____1237) ->
        let fv =
          match lb.FStar_Syntax_Syntax.lbname with
          | FStar_Util.Inr fv -> fv
          | FStar_Util.Inl uu____1252 -> failwith "global Sig_let has bv"  in
        FStar_Reflection_Data.Sg_Let
          (r, fv, (lb.FStar_Syntax_Syntax.lbtyp),
            (lb.FStar_Syntax_Syntax.lbdef))
    | FStar_Syntax_Syntax.Sig_inductive_typ (lid,us,bs,t,uu____1261,c_lids)
        ->
        let nm = FStar_Ident.path_of_lid lid  in
        let uu____1274 =
          let uu____1287 = FStar_List.map FStar_Ident.path_of_lid c_lids  in
          (nm, bs, t, uu____1287)  in
        FStar_Reflection_Data.Sg_Inductive uu____1274
    | FStar_Syntax_Syntax.Sig_datacon (lid,us,t,uu____1303,n1,uu____1305) ->
        let uu____1310 =
          let uu____1315 = FStar_Ident.path_of_lid lid  in (uu____1315, t)
           in
        FStar_Reflection_Data.Sg_Constructor uu____1310
    | uu____1320 -> FStar_Reflection_Data.Unk
  
let (pack_sigelt :
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.sigelt) =
  fun sv  ->
    match sv with
    | FStar_Reflection_Data.Sg_Let (r,fv,ty,def) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inr fv) [] ty
            FStar_Parser_Const.effect_Tot_lid def []
            def.FStar_Syntax_Syntax.pos
           in
        FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt
          (FStar_Syntax_Syntax.Sig_let ((r, [lb]), []))
    | FStar_Reflection_Data.Sg_Constructor uu____1341 ->
        failwith "packing Sg_Constructor, sorry"
    | FStar_Reflection_Data.Sg_Inductive uu____1346 ->
        failwith "packing Sg_Inductive, sorry"
    | FStar_Reflection_Data.Unk  -> failwith "packing Unk, sorry"
  
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (type_of_binder : FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.typ)
  = fun b  -> match b with | (b1,uu____1366) -> b1.FStar_Syntax_Syntax.sort 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____1373 = FStar_Syntax_Util.un_uinst t1  in
      let uu____1374 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____1373 uu____1374
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 