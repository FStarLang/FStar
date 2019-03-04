open Prims
let (env_hook :
  FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (inspect_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Reflection_Data.aqualv) =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu____61704)
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
    let uu____61729 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____61729
  
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns  ->
    let lid = FStar_Parser_Const.p2l ns  in
    let fallback uu____61748 =
      let quals =
        let uu____61752 =
          FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid  in
        if uu____61752
        then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
        else
          (let uu____61759 =
             FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid  in
           if uu____61759
           then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
           else
             (let uu____61766 =
                FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid  in
              if uu____61766
              then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
              else
                (let uu____61773 =
                   FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid  in
                 if uu____61773
                 then
                   FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
                 else FStar_Pervasives_Native.None)))
         in
      let uu____61780 = FStar_Parser_Const.p2l ns  in
      FStar_Syntax_Syntax.lid_as_fv uu____61780
        (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "999"))
        quals
       in
    let uu____61782 = FStar_ST.op_Bang env_hook  in
    match uu____61782 with
    | FStar_Pervasives_Native.None  -> fallback ()
    | FStar_Pervasives_Native.Some env ->
        let qninfo = FStar_TypeChecker_Env.lookup_qname env lid  in
        (match qninfo with
         | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,_us),_rng) ->
             let quals = FStar_Syntax_DsEnv.fv_qual_of_se se  in
             let uu____61862 = FStar_Parser_Const.p2l ns  in
             FStar_Syntax_Syntax.lid_as_fv uu____61862
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "999")) quals
         | uu____61864 -> fallback ())
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____61883::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____61913 = init xs  in x :: uu____61913
  
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____61923) ->
        let uu____61938 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____61938
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____61942) ->
        FStar_Reflection_Data.C_String s
    | FStar_Const.Const_range r -> FStar_Reflection_Data.C_Range r
    | FStar_Const.Const_reify  -> FStar_Reflection_Data.C_Reify
    | FStar_Const.Const_reflect l ->
        let uu____61947 = FStar_Ident.path_of_lid l  in
        FStar_Reflection_Data.C_Reflect uu____61947
    | uu____61948 ->
        let uu____61949 =
          let uu____61951 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____61951  in
        failwith uu____61949
  
let rec (inspect_ln :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    let t3 = FStar_Syntax_Util.unlazy_emb t2  in
    match t3.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t4,uu____61964) -> inspect_ln t4
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Reflection_Data.Tv_Var bv
    | FStar_Syntax_Syntax.Tm_bvar bv -> FStar_Reflection_Data.Tv_BVar bv
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect_ln: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____62022 = last args  in
        (match uu____62022 with
         | (a,q) ->
             let q' = inspect_aqual q  in
             let uu____62050 =
               let uu____62055 =
                 let uu____62056 =
                   let uu____62061 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____62061  in
                 uu____62056 FStar_Pervasives_Native.None
                   t3.FStar_Syntax_Syntax.pos
                  in
               (uu____62055, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____62050)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____62072,uu____62073) ->
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
    | FStar_Syntax_Syntax.Tm_type uu____62165 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect_ln: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____62186 ->
        let uu____62201 = FStar_Syntax_Util.arrow_one t3  in
        (match uu____62201 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
        FStar_Reflection_Data.Tv_Refine (bv, t4)
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____62226 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____62226
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
        let uu____62245 =
          let uu____62250 =
            let uu____62251 =
              FStar_Syntax_Unionfind.uvar_id
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            FStar_BigInt.of_int_fs uu____62251  in
          (uu____62250, (ctx_u, s))  in
        FStar_Reflection_Data.Tv_Uvar uu____62245
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____62283 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (false, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____62309 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (true, bv, (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____62362 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____62362
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____62383 =
                let uu____62390 =
                  FStar_List.map
                    (fun uu____62403  ->
                       match uu____62403 with
                       | (p1,uu____62412) -> inspect_pat p1) ps
                   in
                (fv, uu____62390)  in
              FStar_Reflection_Data.Pat_Cons uu____62383
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term (bv,t5) ->
              FStar_Reflection_Data.Pat_Dot_Term (bv, t5)
           in
        let brs1 =
          FStar_List.map
            (fun uu___522_62463  ->
               match uu___522_62463 with
               | (pat,uu____62485,t5) ->
                   let uu____62503 = inspect_pat pat  in (uu____62503, t5))
            brs
           in
        FStar_Reflection_Data.Tv_Match (t4, brs1)
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Reflection_Data.Tv_Unknown
    | uu____62508 ->
        ((let uu____62510 =
            let uu____62516 =
              let uu____62518 = FStar_Syntax_Print.tag_of_term t3  in
              let uu____62520 = FStar_Syntax_Print.term_to_string t3  in
              FStar_Util.format2
                "inspect_ln: outside of expected syntax (%s, %s)\n"
                uu____62518 uu____62520
               in
            (FStar_Errors.Warning_CantInspect, uu____62516)  in
          FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____62510);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____62531) ->
        FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____62543 =
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
           in
        if uu____62543
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____62547)::(post,uu____62549)::uu____62550 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____62593 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else
          (let uu____62607 =
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Tot_lid
              in
           if uu____62607
           then
             let maybe_dec =
               FStar_List.tryFind
                 (fun uu___523_62615  ->
                    match uu___523_62615 with
                    | FStar_Syntax_Syntax.DECREASES uu____62617 -> true
                    | uu____62621 -> false) ct.FStar_Syntax_Syntax.flags
                in
             let md =
               match maybe_dec with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   t) -> FStar_Pervasives_Native.Some t
               | uu____62631 -> failwith "impossible"  in
             FStar_Reflection_Data.C_Total
               ((ct.FStar_Syntax_Syntax.result_typ), md)
           else FStar_Reflection_Data.C_Unknown)
    | FStar_Syntax_Syntax.GTotal uu____62641 ->
        FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total (t,uu____62657) ->
        FStar_Syntax_Syntax.mk_Total t
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let ct =
          let uu____62665 =
            let uu____62676 = FStar_Syntax_Syntax.as_arg pre  in
            let uu____62685 =
              let uu____62696 = FStar_Syntax_Syntax.as_arg post  in
              [uu____62696]  in
            uu____62676 :: uu____62685  in
          {
            FStar_Syntax_Syntax.comp_univs = [];
            FStar_Syntax_Syntax.effect_name =
              FStar_Parser_Const.effect_Lemma_lid;
            FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
            FStar_Syntax_Syntax.effect_args = uu____62665;
            FStar_Syntax_Syntax.flags = []
          }  in
        FStar_Syntax_Syntax.mk_Comp ct
    | uu____62729 -> failwith "cannot pack a C_Unknown"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____62738 =
          let uu____62750 = FStar_BigInt.string_of_big_int i  in
          (uu____62750, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____62738
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
    | FStar_Reflection_Data.C_Range r -> FStar_Const.Const_range r
    | FStar_Reflection_Data.C_Reify  -> FStar_Const.Const_reify
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____62770 = FStar_Ident.lid_of_path ns FStar_Range.dummyRange
           in
        FStar_Const.Const_reflect uu____62770
  
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
        let uu____62835 =
          let uu____62842 =
            let uu____62843 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____62843  in
          FStar_Syntax_Syntax.mk uu____62842  in
        uu____62835 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
              let uu____62912 =
                let uu____62913 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____62913  in
              FStar_All.pipe_left wrap uu____62912
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____62920 =
                let uu____62921 =
                  let uu____62935 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____62953 = pack_pat p1  in
                         (uu____62953, false)) ps
                     in
                  (fv, uu____62935)  in
                FStar_Syntax_Syntax.Pat_cons uu____62921  in
              FStar_All.pipe_left wrap uu____62920
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
            (fun uu___524_63002  ->
               match uu___524_63002 with
               | (pat,t1) ->
                   let uu____63019 = pack_pat pat  in
                   (uu____63019, FStar_Pervasives_Native.None, t1)) brs
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
      let uu____63180 =
        let uu____63181 = FStar_Syntax_Subst.compress attr  in
        uu____63181.FStar_Syntax_Syntax.n  in
      match uu____63180 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let ses =
            let uu____63190 =
              let uu____63192 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_Ident.text_of_lid uu____63192  in
            FStar_TypeChecker_Env.lookup_attr env uu____63190  in
          FStar_List.concatMap
            (fun se  ->
               let uu____63196 = FStar_Syntax_Util.lid_of_sigelt se  in
               match uu____63196 with
               | FStar_Pervasives_Native.None  -> []
               | FStar_Pervasives_Native.Some l ->
                   let uu____63202 =
                     FStar_Syntax_Syntax.lid_as_fv l
                       (FStar_Syntax_Syntax.Delta_constant_at_level
                          (Prims.parse_int "999"))
                       FStar_Pervasives_Native.None
                      in
                   [uu____63202]) ses
      | uu____63204 -> []
  
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
      let uu___885_63252 = se  in
      {
        FStar_Syntax_Syntax.sigel =
          (uu___885_63252.FStar_Syntax_Syntax.sigel);
        FStar_Syntax_Syntax.sigrng =
          (uu___885_63252.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals =
          (uu___885_63252.FStar_Syntax_Syntax.sigquals);
        FStar_Syntax_Syntax.sigmeta =
          (uu___885_63252.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs = attrs
      }
  
let (inspect_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_Data.sigelt_view) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let ((r,lb::[]),uu____63261) ->
        let fv =
          match lb.FStar_Syntax_Syntax.lbname with
          | FStar_Util.Inr fv -> fv
          | FStar_Util.Inl uu____63272 ->
              failwith "impossible: global Sig_let has bv"
           in
        let uu____63274 =
          FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs
           in
        (match uu____63274 with
         | (s,us) ->
             let typ =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbtyp  in
             let def =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbdef  in
             FStar_Reflection_Data.Sg_Let
               (r, fv, (lb.FStar_Syntax_Syntax.lbunivs),
                 (lb.FStar_Syntax_Syntax.lbtyp),
                 (lb.FStar_Syntax_Syntax.lbdef)))
    | FStar_Syntax_Syntax.Sig_inductive_typ (lid,us,bs,ty,uu____63302,c_lids)
        ->
        let nm = FStar_Ident.path_of_lid lid  in
        let uu____63313 = FStar_Syntax_Subst.univ_var_opening us  in
        (match uu____63313 with
         | (s,us1) ->
             let bs1 = FStar_Syntax_Subst.subst_binders s bs  in
             let ty1 = FStar_Syntax_Subst.subst s ty  in
             let uu____63334 =
               let uu____63351 =
                 FStar_List.map FStar_Ident.path_of_lid c_lids  in
               (nm, us1, bs1, ty1, uu____63351)  in
             FStar_Reflection_Data.Sg_Inductive uu____63334)
    | FStar_Syntax_Syntax.Sig_datacon (lid,us,ty,uu____63363,n1,uu____63365)
        ->
        let uu____63372 = FStar_Syntax_Subst.univ_var_opening us  in
        (match uu____63372 with
         | (s,us1) ->
             let ty1 = FStar_Syntax_Subst.subst s ty  in
             let uu____63392 =
               let uu____63397 = FStar_Ident.path_of_lid lid  in
               (uu____63397, ty1)  in
             FStar_Reflection_Data.Sg_Constructor uu____63392)
    | uu____63398 -> FStar_Reflection_Data.Unk
  
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
        let uu____63424 =
          let uu____63425 =
            let uu____63432 =
              let uu____63435 = FStar_Syntax_Syntax.lid_of_fv fv  in
              [uu____63435]  in
            ((r, [lb]), uu____63432)  in
          FStar_Syntax_Syntax.Sig_let uu____63425  in
        FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt uu____63424
    | FStar_Reflection_Data.Sg_Constructor uu____63441 ->
        failwith "packing Sg_Constructor, sorry"
    | FStar_Reflection_Data.Sg_Inductive uu____63447 ->
        failwith "packing Sg_Inductive, sorry"
    | FStar_Reflection_Data.Unk  -> failwith "packing Unk, sorry"
  
let (inspect_bv : FStar_Syntax_Syntax.bv -> FStar_Reflection_Data.bv_view) =
  fun bv  ->
    let uu____63472 =
      FStar_Ident.string_of_ident bv.FStar_Syntax_Syntax.ppname  in
    let uu____63474 = FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index  in
    {
      FStar_Reflection_Data.bv_ppname = uu____63472;
      FStar_Reflection_Data.bv_index = uu____63474;
      FStar_Reflection_Data.bv_sort = (bv.FStar_Syntax_Syntax.sort)
    }
  
let (pack_bv : FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.bv) =
  fun bvv  ->
    let uu____63481 =
      FStar_Ident.mk_ident
        ((bvv.FStar_Reflection_Data.bv_ppname), FStar_Range.dummyRange)
       in
    let uu____63483 =
      FStar_BigInt.to_int_fs bvv.FStar_Reflection_Data.bv_index  in
    {
      FStar_Syntax_Syntax.ppname = uu____63481;
      FStar_Syntax_Syntax.index = uu____63483;
      FStar_Syntax_Syntax.sort = (bvv.FStar_Reflection_Data.bv_sort)
    }
  
let (inspect_binder :
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.bv * FStar_Reflection_Data.aqualv))
  =
  fun b  ->
    let uu____63499 = b  in
    match uu____63499 with
    | (bv,aq) -> let uu____63510 = inspect_aqual aq  in (bv, uu____63510)
  
let (pack_binder :
  FStar_Syntax_Syntax.bv ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.binder)
  =
  fun bv  ->
    fun aqv  -> let uu____63522 = pack_aqual aqv  in (bv, uu____63522)
  
let (moduleof : FStar_TypeChecker_Env.env -> Prims.string Prims.list) =
  fun e  -> FStar_Ident.path_of_lid e.FStar_TypeChecker_Env.curmodule 
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____63557 = FStar_Syntax_Util.un_uinst t1  in
      let uu____63558 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____63557 uu____63558
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 