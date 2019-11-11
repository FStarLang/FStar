open Prims
let (env_hook :
  FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (inspect_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Reflection_Data.aqualv) =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu____12) ->
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
    let uu____37 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____37
  
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns  ->
    let lid = FStar_Parser_Const.p2l ns  in
    let fallback uu____56 =
      let quals =
        let uu____60 = FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid
           in
        if uu____60
        then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
        else
          (let uu____67 =
             FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid  in
           if uu____67
           then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
           else
             (let uu____74 =
                FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid  in
              if uu____74
              then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
              else
                (let uu____81 =
                   FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid  in
                 if uu____81
                 then
                   FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
                 else FStar_Pervasives_Native.None)))
         in
      let uu____88 = FStar_Parser_Const.p2l ns  in
      FStar_Syntax_Syntax.lid_as_fv uu____88
        (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (999)))
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
             let uu____170 = FStar_Parser_Const.p2l ns  in
             FStar_Syntax_Syntax.lid_as_fv uu____170
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.of_int (999))) quals
         | uu____172 -> fallback ())
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____191::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____221 = init xs  in x :: uu____221
  
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____231) ->
        let uu____246 = FStar_BigInt.big_int_of_string s  in
        FStar_Reflection_Data.C_Int uu____246
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____250) ->
        FStar_Reflection_Data.C_String s
    | FStar_Const.Const_range r -> FStar_Reflection_Data.C_Range r
    | FStar_Const.Const_reify  -> FStar_Reflection_Data.C_Reify
    | FStar_Const.Const_reflect l ->
        let uu____255 = FStar_Ident.path_of_lid l  in
        FStar_Reflection_Data.C_Reflect uu____255
    | uu____256 ->
        let uu____257 =
          let uu____259 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____259  in
        failwith uu____257
  
let rec (inspect_ln :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    let t3 = FStar_Syntax_Util.unlazy_emb t2  in
    match t3.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t4,uu____272) -> inspect_ln t4
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Reflection_Data.Tv_Var bv
    | FStar_Syntax_Syntax.Tm_bvar bv -> FStar_Reflection_Data.Tv_BVar bv
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect_ln: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____330 = last args  in
        (match uu____330 with
         | (a,q) ->
             let q' = inspect_aqual q  in
             let uu____358 =
               let uu____363 =
                 let uu____364 =
                   let uu____369 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____369  in
                 uu____364 FStar_Pervasives_Native.None
                   t3.FStar_Syntax_Syntax.pos
                  in
               (uu____363, (a, q'))  in
             FStar_Reflection_Data.Tv_App uu____358)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____378,uu____379) ->
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
    | FStar_Syntax_Syntax.Tm_type uu____471 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect_ln: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____492 ->
        let uu____507 = FStar_Syntax_Util.arrow_one t3  in
        (match uu____507 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
        FStar_Reflection_Data.Tv_Refine (bv, t4)
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____532 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____532
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
        let uu____551 =
          let uu____556 =
            let uu____557 =
              FStar_Syntax_Unionfind.uvar_id
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            FStar_BigInt.of_int_fs uu____557  in
          (uu____556, (ctx_u, s))  in
        FStar_Reflection_Data.Tv_Uvar uu____551
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____589 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (false, (lb.FStar_Syntax_Syntax.lbattrs), bv,
                   (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____617 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (true, (lb.FStar_Syntax_Syntax.lbattrs), bv,
                   (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____672 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____672
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____693 =
                let uu____705 =
                  FStar_List.map
                    (fun uu____729  ->
                       match uu____729 with
                       | (p1,b) ->
                           let uu____750 = inspect_pat p1  in (uu____750, b))
                    ps
                   in
                (fv, uu____705)  in
              FStar_Reflection_Data.Pat_Cons uu____693
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term (bv,t5) ->
              FStar_Reflection_Data.Pat_Dot_Term (bv, t5)
           in
        let brs1 =
          FStar_List.map
            (fun uu___0_801  ->
               match uu___0_801 with
               | (pat,uu____823,t5) ->
                   let uu____841 = inspect_pat pat  in (uu____841, t5)) brs
           in
        FStar_Reflection_Data.Tv_Match (t4, brs1)
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Reflection_Data.Tv_Unknown
    | uu____846 ->
        ((let uu____848 =
            let uu____854 =
              let uu____856 = FStar_Syntax_Print.tag_of_term t3  in
              let uu____858 = FStar_Syntax_Print.term_to_string t3  in
              FStar_Util.format2
                "inspect_ln: outside of expected syntax (%s, %s)\n" uu____856
                uu____858
               in
            (FStar_Errors.Warning_CantInspect, uu____854)  in
          FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____848);
         FStar_Reflection_Data.Tv_Unknown)
  
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____869) ->
        FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____881 =
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
           in
        if uu____881
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____885)::(post,uu____887)::uu____888 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____931 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else
          (let uu____945 =
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Tot_lid
              in
           if uu____945
           then
             let maybe_dec =
               FStar_List.tryFind
                 (fun uu___1_953  ->
                    match uu___1_953 with
                    | FStar_Syntax_Syntax.DECREASES uu____955 -> true
                    | uu____959 -> false) ct.FStar_Syntax_Syntax.flags
                in
             let md =
               match maybe_dec with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   t) -> FStar_Pervasives_Native.Some t
               | uu____969 -> failwith "impossible"  in
             FStar_Reflection_Data.C_Total
               ((ct.FStar_Syntax_Syntax.result_typ), md)
           else FStar_Reflection_Data.C_Unknown)
    | FStar_Syntax_Syntax.GTotal uu____979 -> FStar_Reflection_Data.C_Unknown
  
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total (t,uu____995) ->
        FStar_Syntax_Syntax.mk_Total t
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let ct =
          let uu____1003 =
            let uu____1014 = FStar_Syntax_Syntax.as_arg pre  in
            let uu____1023 =
              let uu____1034 = FStar_Syntax_Syntax.as_arg post  in
              [uu____1034]  in
            uu____1014 :: uu____1023  in
          {
            FStar_Syntax_Syntax.comp_univs = [];
            FStar_Syntax_Syntax.effect_name =
              FStar_Parser_Const.effect_Lemma_lid;
            FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
            FStar_Syntax_Syntax.effect_args = uu____1003;
            FStar_Syntax_Syntax.flags = []
          }  in
        FStar_Syntax_Syntax.mk_Comp ct
    | uu____1067 -> failwith "cannot pack a C_Unknown"
  
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____1076 =
          let uu____1088 = FStar_BigInt.string_of_big_int i  in
          (uu____1088, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____1076
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
    | FStar_Reflection_Data.C_Range r -> FStar_Const.Const_range r
    | FStar_Reflection_Data.C_Reify  -> FStar_Const.Const_reify
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____1108 = FStar_Ident.lid_of_path ns FStar_Range.dummyRange
           in
        FStar_Const.Const_reflect uu____1108
  
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
        let uu____1173 =
          let uu____1180 =
            let uu____1181 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____1181  in
          FStar_Syntax_Syntax.mk uu____1180  in
        uu____1173 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,ctx_u_s) ->
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (false ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let ((false, [lb]), t2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (true ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
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
              let uu____1253 =
                let uu____1254 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____1254  in
              FStar_All.pipe_left wrap uu____1253
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____1271 =
                let uu____1272 =
                  let uu____1286 =
                    FStar_List.map
                      (fun uu____1310  ->
                         match uu____1310 with
                         | (p1,b) ->
                             let uu____1325 = pack_pat p1  in (uu____1325, b))
                      ps
                     in
                  (fv, uu____1286)  in
                FStar_Syntax_Syntax.Pat_cons uu____1272  in
              FStar_All.pipe_left wrap uu____1271
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
            (fun uu___2_1373  ->
               match uu___2_1373 with
               | (pat,t1) ->
                   let uu____1390 = pack_pat pat  in
                   (uu____1390, FStar_Pervasives_Native.None, t1)) brs
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
      if n1 < Prims.int_zero
      then FStar_Order.Lt
      else if n1 = Prims.int_zero then FStar_Order.Eq else FStar_Order.Gt
  
let (is_free :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun x  -> fun t  -> FStar_Syntax_Util.is_free_in x t 
let (lookup_attr :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv Prims.list)
  =
  fun attr  ->
    fun env  ->
      let uu____1551 =
        let uu____1552 = FStar_Syntax_Subst.compress attr  in
        uu____1552.FStar_Syntax_Syntax.n  in
      match uu____1551 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let ses =
            let uu____1561 =
              let uu____1563 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_Ident.text_of_lid uu____1563  in
            FStar_TypeChecker_Env.lookup_attr env uu____1561  in
          FStar_List.concatMap
            (fun se  ->
               let uu____1567 = FStar_Syntax_Util.lid_of_sigelt se  in
               match uu____1567 with
               | FStar_Pervasives_Native.None  -> []
               | FStar_Pervasives_Native.Some l ->
                   let uu____1573 =
                     FStar_Syntax_Syntax.lid_as_fv l
                       (FStar_Syntax_Syntax.Delta_constant_at_level
                          (Prims.of_int (999))) FStar_Pervasives_Native.None
                      in
                   [uu____1573]) ses
      | uu____1575 -> []
  
let (all_defs_in_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv Prims.list) =
  fun env  ->
    let uu____1586 = FStar_TypeChecker_Env.lidents env  in
    FStar_List.map
      (fun l  ->
         FStar_Syntax_Syntax.lid_as_fv l
           (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (999)))
           FStar_Pervasives_Native.None) uu____1586
  
let (defs_in_module :
  FStar_TypeChecker_Env.env ->
    FStar_Reflection_Data.name -> FStar_Syntax_Syntax.fv Prims.list)
  =
  fun env  ->
    fun modul  ->
      let uu____1607 = FStar_TypeChecker_Env.lidents env  in
      FStar_List.concatMap
        (fun l  ->
           let ns =
             let uu____1615 =
               let uu____1618 = FStar_Ident.ids_of_lid l  in
               FStar_All.pipe_right uu____1618 init  in
             FStar_All.pipe_right uu____1615
               (FStar_List.map FStar_Ident.string_of_ident)
              in
           if ns = modul
           then
             let uu____1631 =
               FStar_Syntax_Syntax.lid_as_fv l
                 (FStar_Syntax_Syntax.Delta_constant_at_level
                    (Prims.of_int (999))) FStar_Pervasives_Native.None
                in
             [uu____1631]
           else []) uu____1607
  
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
      let uu___376_1682 = se  in
      {
        FStar_Syntax_Syntax.sigel = (uu___376_1682.FStar_Syntax_Syntax.sigel);
        FStar_Syntax_Syntax.sigrng =
          (uu___376_1682.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals =
          (uu___376_1682.FStar_Syntax_Syntax.sigquals);
        FStar_Syntax_Syntax.sigmeta =
          (uu___376_1682.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs = attrs;
        FStar_Syntax_Syntax.sigopts =
          (uu___376_1682.FStar_Syntax_Syntax.sigopts)
      }
  
let (rd_to_syntax_qual :
  FStar_Reflection_Data.qualifier -> FStar_Syntax_Syntax.qualifier) =
  fun uu___3_1688  ->
    match uu___3_1688 with
    | FStar_Reflection_Data.Assumption  -> FStar_Syntax_Syntax.Assumption
    | FStar_Reflection_Data.New  -> FStar_Syntax_Syntax.New
    | FStar_Reflection_Data.Private  -> FStar_Syntax_Syntax.Private
    | FStar_Reflection_Data.Unfold_for_unification_and_vcgen  ->
        FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
    | FStar_Reflection_Data.Visible_default  ->
        FStar_Syntax_Syntax.Visible_default
    | FStar_Reflection_Data.Irreducible  -> FStar_Syntax_Syntax.Irreducible
    | FStar_Reflection_Data.Abstract  -> FStar_Syntax_Syntax.Abstract
    | FStar_Reflection_Data.Inline_for_extraction  ->
        FStar_Syntax_Syntax.Inline_for_extraction
    | FStar_Reflection_Data.NoExtract  -> FStar_Syntax_Syntax.NoExtract
    | FStar_Reflection_Data.Noeq  -> FStar_Syntax_Syntax.Noeq
    | FStar_Reflection_Data.Unopteq  -> FStar_Syntax_Syntax.Unopteq
    | FStar_Reflection_Data.TotalEffect  -> FStar_Syntax_Syntax.TotalEffect
    | FStar_Reflection_Data.Logic  -> FStar_Syntax_Syntax.Logic
    | FStar_Reflection_Data.Reifiable  -> FStar_Syntax_Syntax.Reifiable
    | FStar_Reflection_Data.Reflectable l ->
        FStar_Syntax_Syntax.Reflectable l
    | FStar_Reflection_Data.Discriminator l ->
        FStar_Syntax_Syntax.Discriminator l
    | FStar_Reflection_Data.Projector (l,i) ->
        FStar_Syntax_Syntax.Projector (l, i)
    | FStar_Reflection_Data.RecordType (l1,l2) ->
        FStar_Syntax_Syntax.RecordType (l1, l2)
    | FStar_Reflection_Data.RecordConstructor (l1,l2) ->
        FStar_Syntax_Syntax.RecordConstructor (l1, l2)
    | FStar_Reflection_Data.Action l -> FStar_Syntax_Syntax.Action l
    | FStar_Reflection_Data.ExceptionConstructor  ->
        FStar_Syntax_Syntax.ExceptionConstructor
    | FStar_Reflection_Data.HasMaskedEffect  ->
        FStar_Syntax_Syntax.HasMaskedEffect
    | FStar_Reflection_Data.Effect  -> FStar_Syntax_Syntax.Effect
    | FStar_Reflection_Data.OnlyName  -> FStar_Syntax_Syntax.OnlyName
  
let (syntax_to_rd_qual :
  FStar_Syntax_Syntax.qualifier -> FStar_Reflection_Data.qualifier) =
  fun uu___4_1727  ->
    match uu___4_1727 with
    | FStar_Syntax_Syntax.Assumption  -> FStar_Reflection_Data.Assumption
    | FStar_Syntax_Syntax.New  -> FStar_Reflection_Data.New
    | FStar_Syntax_Syntax.Private  -> FStar_Reflection_Data.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        FStar_Reflection_Data.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  ->
        FStar_Reflection_Data.Visible_default
    | FStar_Syntax_Syntax.Irreducible  -> FStar_Reflection_Data.Irreducible
    | FStar_Syntax_Syntax.Abstract  -> FStar_Reflection_Data.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        FStar_Reflection_Data.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract  -> FStar_Reflection_Data.NoExtract
    | FStar_Syntax_Syntax.Noeq  -> FStar_Reflection_Data.Noeq
    | FStar_Syntax_Syntax.Unopteq  -> FStar_Reflection_Data.Unopteq
    | FStar_Syntax_Syntax.TotalEffect  -> FStar_Reflection_Data.TotalEffect
    | FStar_Syntax_Syntax.Logic  -> FStar_Reflection_Data.Logic
    | FStar_Syntax_Syntax.Reifiable  -> FStar_Reflection_Data.Reifiable
    | FStar_Syntax_Syntax.Reflectable l ->
        FStar_Reflection_Data.Reflectable l
    | FStar_Syntax_Syntax.Discriminator l ->
        FStar_Reflection_Data.Discriminator l
    | FStar_Syntax_Syntax.Projector (l,i) ->
        FStar_Reflection_Data.Projector (l, i)
    | FStar_Syntax_Syntax.RecordType (l1,l2) ->
        FStar_Reflection_Data.RecordType (l1, l2)
    | FStar_Syntax_Syntax.RecordConstructor (l1,l2) ->
        FStar_Reflection_Data.RecordConstructor (l1, l2)
    | FStar_Syntax_Syntax.Action l -> FStar_Reflection_Data.Action l
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Reflection_Data.ExceptionConstructor
    | FStar_Syntax_Syntax.HasMaskedEffect  ->
        FStar_Reflection_Data.HasMaskedEffect
    | FStar_Syntax_Syntax.Effect  -> FStar_Reflection_Data.Effect
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Reflection_Data.OnlyName
  
let (sigelt_quals :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_Data.qualifier Prims.list) =
  fun se  ->
    FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
      (FStar_List.map syntax_to_rd_qual)
  
let (set_sigelt_quals :
  FStar_Reflection_Data.qualifier Prims.list ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun quals  ->
    fun se  ->
      let uu___455_1790 = se  in
      let uu____1791 = FStar_List.map rd_to_syntax_qual quals  in
      {
        FStar_Syntax_Syntax.sigel = (uu___455_1790.FStar_Syntax_Syntax.sigel);
        FStar_Syntax_Syntax.sigrng =
          (uu___455_1790.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals = uu____1791;
        FStar_Syntax_Syntax.sigmeta =
          (uu___455_1790.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs =
          (uu___455_1790.FStar_Syntax_Syntax.sigattrs);
        FStar_Syntax_Syntax.sigopts =
          (uu___455_1790.FStar_Syntax_Syntax.sigopts)
      }
  
let (e_optionstate_hook :
  FStar_Options.optionstate FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (sigelt_opts :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigopts with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some o ->
        let uu____1824 =
          let uu____1825 =
            let uu____1832 =
              let uu____1835 = FStar_ST.op_Bang e_optionstate_hook  in
              FStar_All.pipe_right uu____1835 FStar_Util.must  in
            FStar_Syntax_Embeddings.embed uu____1832 o  in
          uu____1825 FStar_Range.dummyRange FStar_Pervasives_Native.None
            FStar_Syntax_Embeddings.id_norm_cb
           in
        FStar_Pervasives_Native.Some uu____1824
  
let (inspect_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_Data.sigelt_view) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let ((r,lb::[]),uu____1885) ->
        let fv =
          match lb.FStar_Syntax_Syntax.lbname with
          | FStar_Util.Inr fv -> fv
          | FStar_Util.Inl uu____1896 ->
              failwith "impossible: global Sig_let has bv"
           in
        let uu____1898 =
          FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs
           in
        (match uu____1898 with
         | (s,us) ->
             let typ =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbtyp  in
             let def =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbdef  in
             FStar_Reflection_Data.Sg_Let
               (r, fv, (lb.FStar_Syntax_Syntax.lbunivs),
                 (lb.FStar_Syntax_Syntax.lbtyp),
                 (lb.FStar_Syntax_Syntax.lbdef)))
    | FStar_Syntax_Syntax.Sig_inductive_typ (lid,us,bs,ty,uu____1926,c_lids)
        ->
        let nm = FStar_Ident.path_of_lid lid  in
        let uu____1937 = FStar_Syntax_Subst.univ_var_opening us  in
        (match uu____1937 with
         | (s,us1) ->
             let bs1 = FStar_Syntax_Subst.subst_binders s bs  in
             let ty1 = FStar_Syntax_Subst.subst s ty  in
             let uu____1958 =
               let uu____1975 = FStar_List.map FStar_Ident.path_of_lid c_lids
                  in
               (nm, us1, bs1, ty1, uu____1975)  in
             FStar_Reflection_Data.Sg_Inductive uu____1958)
    | FStar_Syntax_Syntax.Sig_datacon (lid,us,ty,uu____1987,n1,uu____1989) ->
        let uu____1996 = FStar_Syntax_Subst.univ_var_opening us  in
        (match uu____1996 with
         | (s,us1) ->
             let ty1 = FStar_Syntax_Subst.subst s ty  in
             let uu____2016 =
               let uu____2021 = FStar_Ident.path_of_lid lid  in
               (uu____2021, ty1)  in
             FStar_Reflection_Data.Sg_Constructor uu____2016)
    | uu____2022 -> FStar_Reflection_Data.Unk
  
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
        let uu____2048 =
          let uu____2049 =
            let uu____2056 =
              let uu____2059 = FStar_Syntax_Syntax.lid_of_fv fv  in
              [uu____2059]  in
            ((r, [lb]), uu____2056)  in
          FStar_Syntax_Syntax.Sig_let uu____2049  in
        FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt uu____2048
    | FStar_Reflection_Data.Sg_Constructor uu____2065 ->
        failwith "packing Sg_Constructor, sorry"
    | FStar_Reflection_Data.Sg_Inductive uu____2071 ->
        failwith "packing Sg_Inductive, sorry"
    | FStar_Reflection_Data.Unk  -> failwith "packing Unk, sorry"
  
let (inspect_bv : FStar_Syntax_Syntax.bv -> FStar_Reflection_Data.bv_view) =
  fun bv  ->
    let uu____2096 =
      FStar_Ident.string_of_ident bv.FStar_Syntax_Syntax.ppname  in
    let uu____2098 = FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index  in
    {
      FStar_Reflection_Data.bv_ppname = uu____2096;
      FStar_Reflection_Data.bv_index = uu____2098;
      FStar_Reflection_Data.bv_sort = (bv.FStar_Syntax_Syntax.sort)
    }
  
let (pack_bv : FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.bv) =
  fun bvv  ->
    let uu____2105 =
      FStar_Ident.mk_ident
        ((bvv.FStar_Reflection_Data.bv_ppname), FStar_Range.dummyRange)
       in
    let uu____2107 =
      FStar_BigInt.to_int_fs bvv.FStar_Reflection_Data.bv_index  in
    {
      FStar_Syntax_Syntax.ppname = uu____2105;
      FStar_Syntax_Syntax.index = uu____2107;
      FStar_Syntax_Syntax.sort = (bvv.FStar_Reflection_Data.bv_sort)
    }
  
let (inspect_binder :
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.bv * FStar_Reflection_Data.aqualv))
  =
  fun b  ->
    let uu____2123 = b  in
    match uu____2123 with
    | (bv,aq) -> let uu____2134 = inspect_aqual aq  in (bv, uu____2134)
  
let (pack_binder :
  FStar_Syntax_Syntax.bv ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.binder)
  =
  fun bv  -> fun aqv  -> let uu____2146 = pack_aqual aqv  in (bv, uu____2146) 
let (moduleof : FStar_TypeChecker_Env.env -> Prims.string Prims.list) =
  fun e  -> FStar_Ident.path_of_lid e.FStar_TypeChecker_Env.curmodule 
let (env_open_modules :
  FStar_TypeChecker_Env.env -> FStar_Reflection_Data.name Prims.list) =
  fun e  ->
    let uu____2173 =
      FStar_Syntax_DsEnv.open_modules e.FStar_TypeChecker_Env.dsenv  in
    FStar_List.map
      (fun uu____2191  ->
         match uu____2191 with
         | (l,m) ->
             let uu____2201 = FStar_Ident.ids_of_lid l  in
             FStar_List.map FStar_Ident.text_of_id uu____2201) uu____2173
  
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e  -> FStar_TypeChecker_Env.all_binders e 
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let uu____2223 = FStar_Syntax_Util.un_uinst t1  in
      let uu____2224 = FStar_Syntax_Util.un_uinst t2  in
      FStar_Syntax_Util.term_eq uu____2223 uu____2224
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 
let (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  -> FStar_Syntax_Print.comp_to_string c 