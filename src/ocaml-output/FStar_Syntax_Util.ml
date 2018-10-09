open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____38 = FStar_ST.op_Bang tts_f  in
    match uu____38 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____102 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____102 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____109 =
      let uu____112 =
        let uu____115 =
          FStar_Ident.mk_ident
            ((Prims.strcat FStar_Ident.reserved_prefix
                (Prims.strcat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____115]  in
      FStar_List.append lid.FStar_Ident.ns uu____112  in
    FStar_Ident.lid_of_ids uu____109
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____133 .
    (FStar_Syntax_Syntax.bv,'Auu____133) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term,'Auu____133) FStar_Pervasives_Native.tuple2
  =
  fun uu____146  ->
    match uu____146 with
    | (b,imp) ->
        let uu____153 = FStar_Syntax_Syntax.bv_to_name b  in (uu____153, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____205 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____205
            then []
            else (let uu____224 = arg_of_non_null_binder b  in [uu____224])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  =
  fun binders  ->
    let uu____259 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____341 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____341
              then
                let b1 =
                  let uu____367 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____367, (FStar_Pervasives_Native.snd b))  in
                let uu____374 = arg_of_non_null_binder b1  in (b1, uu____374)
              else
                (let uu____397 = arg_of_non_null_binder b  in (b, uu____397))))
       in
    FStar_All.pipe_right uu____259 FStar_List.unzip
  
let (name_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____531 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____531
              then
                let uu____540 = b  in
                match uu____540 with
                | (a,imp) ->
                    let b1 =
                      let uu____560 =
                        let uu____562 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____562  in
                      FStar_Ident.id_of_text uu____560  in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      }  in
                    (b2, imp)
              else b))
  
let (name_function_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____607 =
          let uu____614 =
            let uu____615 =
              let uu____630 = name_binders binders  in (uu____630, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____615  in
          FStar_Syntax_Syntax.mk uu____614  in
        uu____607 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____652 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____689  ->
            match uu____689 with
            | (t,imp) ->
                let uu____700 =
                  let uu____701 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____701
                   in
                (uu____700, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____756  ->
            match uu____756 with
            | (t,imp) ->
                let uu____773 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____773, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____786 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____786
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____798 . 'Auu____798 -> 'Auu____798 Prims.list =
  fun s  -> [s] 
let (subst_of_list :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.subst_t)
  =
  fun formals  ->
    fun actuals  ->
      if (FStar_List.length formals) = (FStar_List.length actuals)
      then
        FStar_List.fold_right2
          (fun f  ->
             fun a  ->
               fun out  ->
                 (FStar_Syntax_Syntax.NT
                    ((FStar_Pervasives_Native.fst f),
                      (FStar_Pervasives_Native.fst a)))
                 :: out) formals actuals []
      else failwith "Ill-formed substitution"
  
let (rename_binders :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t)
  =
  fun replace_xs  ->
    fun with_ys  ->
      if (FStar_List.length replace_xs) = (FStar_List.length with_ys)
      then
        FStar_List.map2
          (fun uu____924  ->
             fun uu____925  ->
               match (uu____924, uu____925) with
               | ((x,uu____951),(y,uu____953)) ->
                   let uu____974 =
                     let uu____981 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____981)  in
                   FStar_Syntax_Syntax.NT uu____974) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____997) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1003,uu____1004) -> unmeta e2
    | uu____1045 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____1059 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____1066 -> e1
         | uu____1075 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1077,uu____1078) ->
        unmeta_safe e2
    | uu____1119 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____1138 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____1141 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1155 = univ_kernel u1  in
        (match uu____1155 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____1172 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____1181 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____1196 = univ_kernel u  in FStar_Pervasives_Native.snd uu____1196
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____1216,uu____1217) ->
          failwith "Impossible: compare_univs"
      | (uu____1221,FStar_Syntax_Syntax.U_bvar uu____1222) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____1227) ->
          ~- (Prims.parse_int "1")
      | (uu____1229,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____1232) -> ~- (Prims.parse_int "1")
      | (uu____1234,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____1238,FStar_Syntax_Syntax.U_unif
         uu____1239) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____1249,FStar_Syntax_Syntax.U_name
         uu____1250) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____1278 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____1280 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____1278 - uu____1280
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____1316 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____1316
                 (fun uu____1332  ->
                    match uu____1332 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1360,uu____1361) ->
          ~- (Prims.parse_int "1")
      | (uu____1365,FStar_Syntax_Syntax.U_max uu____1366) ->
          (Prims.parse_int "1")
      | uu____1370 ->
          let uu____1375 = univ_kernel u1  in
          (match uu____1375 with
           | (k1,n1) ->
               let uu____1386 = univ_kernel u2  in
               (match uu____1386 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1417 = compare_univs u1 u2  in
      uu____1417 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1436 =
        let uu____1437 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1437;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1436
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1457 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1466 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1489 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1498 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1525 =
          let uu____1526 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1526  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1525;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1555 =
          let uu____1556 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1556  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1555;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
  
let (comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    fun f  ->
      let uu___125_1592 = c  in
      let uu____1593 =
        let uu____1594 =
          let uu___126_1595 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___126_1595.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___126_1595.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___126_1595.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___126_1595.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1594  in
      {
        FStar_Syntax_Syntax.n = uu____1593;
        FStar_Syntax_Syntax.pos = (uu___125_1592.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___125_1592.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1621 -> c
        | FStar_Syntax_Syntax.GTotal uu____1630 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___127_1641 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___127_1641.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___127_1641.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___127_1641.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___127_1641.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___128_1642 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___128_1642.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___128_1642.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1645  ->
           let uu____1646 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1646)
  
let (comp_to_comp_typ :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | uu____1686 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1701 -> true
    | FStar_Syntax_Syntax.GTotal uu____1711 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___112_1736  ->
               match uu___112_1736 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1740 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___113_1753  ->
               match uu___113_1753 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1757 -> false)))
  
let (is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
        FStar_Parser_Const.effect_Tot_lid)
       ||
       (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
          FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___114_1770  ->
               match uu___114_1770 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1774 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___115_1791  ->
            match uu___115_1791 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1795 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___116_1808  ->
            match uu___116_1808 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1812 -> false))
  
let (is_tot_or_gtot_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (is_total_comp c) ||
      (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid
         (comp_effect_name c))
  
let (is_pure_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)
  
let (is_pure_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1844 -> true
    | FStar_Syntax_Syntax.GTotal uu____1854 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___117_1869  ->
                   match uu___117_1869 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1872 -> false)))
  
let (is_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)
  
let (is_div_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)
  
let (is_pure_or_ghost_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  -> (is_pure_comp c) || (is_ghost_effect (comp_effect_name c)) 
let (is_pure_or_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  -> (is_pure_effect l) || (is_ghost_effect l) 
let (is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___118_1917  ->
               match uu___118_1917 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1920 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1936 =
      let uu____1937 = FStar_Syntax_Subst.compress t  in
      uu____1937.FStar_Syntax_Syntax.n  in
    match uu____1936 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1941,c) -> is_pure_or_ghost_comp c
    | uu____1963 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1978 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1987 =
      let uu____1988 = FStar_Syntax_Subst.compress t  in
      uu____1988.FStar_Syntax_Syntax.n  in
    match uu____1987 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1992,c) -> is_lemma_comp c
    | uu____2014 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2022 =
      let uu____2023 = FStar_Syntax_Subst.compress t  in
      uu____2023.FStar_Syntax_Syntax.n  in
    match uu____2022 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____2027) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____2053) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2090,t1,uu____2092) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2118,uu____2119) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2161) -> head_of t1
    | uu____2166 -> t
  
let (head_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax,
                                                            FStar_Syntax_Syntax.arg_qualifier
                                                              FStar_Pervasives_Native.option)
                                                            FStar_Pervasives_Native.tuple2
                                                            Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____2244 -> (t1, [])
  
let rec (head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.term'
                                 FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                              FStar_Pervasives_Native.option)
                                FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____2326 = head_and_args' head1  in
        (match uu____2326 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____2395 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2422) ->
        FStar_Syntax_Subst.compress t2
    | uu____2427 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2435 =
      let uu____2436 = FStar_Syntax_Subst.compress t  in
      uu____2436.FStar_Syntax_Syntax.n  in
    match uu____2435 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____2440,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____2468)::uu____2469 ->
                  let pats' = unmeta pats  in
                  let uu____2529 = head_and_args pats'  in
                  (match uu____2529 with
                   | (head1,uu____2548) ->
                       let uu____2573 =
                         let uu____2574 = un_uinst head1  in
                         uu____2574.FStar_Syntax_Syntax.n  in
                       (match uu____2573 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____2579 -> false))
              | uu____2581 -> false)
         | uu____2593 -> false)
    | uu____2595 -> false
  
let (is_ml_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
           FStar_Parser_Const.effect_ML_lid)
          ||
          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___119_2614  ->
                   match uu___119_2614 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2617 -> false)))
    | uu____2619 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2636) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2646) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2675 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2684 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___129_2696 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___129_2696.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___129_2696.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___129_2696.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___129_2696.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2710  ->
           let uu____2711 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____2711 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___120_2729  ->
            match uu___120_2729 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2733 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2741 -> []
    | FStar_Syntax_Syntax.GTotal uu____2758 -> []
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.effect_args
  
let (primops : FStar_Ident.lident Prims.list) =
  [FStar_Parser_Const.op_Eq;
  FStar_Parser_Const.op_notEq;
  FStar_Parser_Const.op_LT;
  FStar_Parser_Const.op_LTE;
  FStar_Parser_Const.op_GT;
  FStar_Parser_Const.op_GTE;
  FStar_Parser_Const.op_Subtraction;
  FStar_Parser_Const.op_Minus;
  FStar_Parser_Const.op_Addition;
  FStar_Parser_Const.op_Multiply;
  FStar_Parser_Const.op_Division;
  FStar_Parser_Const.op_Modulus;
  FStar_Parser_Const.op_And;
  FStar_Parser_Const.op_Or;
  FStar_Parser_Const.op_Negation] 
let (is_primop_lid : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    FStar_All.pipe_right primops
      (FStar_Util.for_some (FStar_Ident.lid_equals l))
  
let (is_primop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_primop_lid (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____2802 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2812,uu____2813) ->
        unascribe e2
    | uu____2854 -> e1
  
let rec (ascribe :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.comp'
                                                             FStar_Syntax_Syntax.syntax)
       FStar_Util.either,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun k  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2907,uu____2908) ->
          ascribe t' k
      | uu____2949 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2976 =
      let uu____2985 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2985  in
    uu____2976 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3041 =
      let uu____3042 = FStar_Syntax_Subst.compress t  in
      uu____3042.FStar_Syntax_Syntax.n  in
    match uu____3041 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____3046 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____3046
    | uu____3047 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3054 =
      let uu____3055 = FStar_Syntax_Subst.compress t  in
      uu____3055.FStar_Syntax_Syntax.n  in
    match uu____3054 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____3059 ->
             let uu____3068 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____3068
         | uu____3069 -> t)
    | uu____3070 -> t
  
let (eq_lazy_kind :
  FStar_Syntax_Syntax.lazy_kind ->
    FStar_Syntax_Syntax.lazy_kind -> Prims.bool)
  =
  fun k  ->
    fun k'  ->
      match (k, k') with
      | (FStar_Syntax_Syntax.BadLazy ,FStar_Syntax_Syntax.BadLazy ) -> true
      | (FStar_Syntax_Syntax.Lazy_bv ,FStar_Syntax_Syntax.Lazy_bv ) -> true
      | (FStar_Syntax_Syntax.Lazy_binder ,FStar_Syntax_Syntax.Lazy_binder )
          -> true
      | (FStar_Syntax_Syntax.Lazy_fvar ,FStar_Syntax_Syntax.Lazy_fvar ) ->
          true
      | (FStar_Syntax_Syntax.Lazy_comp ,FStar_Syntax_Syntax.Lazy_comp ) ->
          true
      | (FStar_Syntax_Syntax.Lazy_env ,FStar_Syntax_Syntax.Lazy_env ) -> true
      | (FStar_Syntax_Syntax.Lazy_proofstate
         ,FStar_Syntax_Syntax.Lazy_proofstate ) -> true
      | (FStar_Syntax_Syntax.Lazy_goal ,FStar_Syntax_Syntax.Lazy_goal ) ->
          true
      | (FStar_Syntax_Syntax.Lazy_sigelt ,FStar_Syntax_Syntax.Lazy_sigelt )
          -> true
      | (FStar_Syntax_Syntax.Lazy_uvar ,FStar_Syntax_Syntax.Lazy_uvar ) ->
          true
      | uu____3094 -> false
  
let rec unlazy_as_t :
  'Auu____3107 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____3107
  =
  fun k  ->
    fun t  ->
      let uu____3118 =
        let uu____3119 = FStar_Syntax_Subst.compress t  in
        uu____3119.FStar_Syntax_Syntax.n  in
      match uu____3118 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____3124;
            FStar_Syntax_Syntax.rng = uu____3125;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____3128 -> failwith "Not a Tm_lazy of the expected kind"
  
let mk_lazy :
  'a .
    'a ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.lazy_kind ->
          FStar_Range.range FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun typ  ->
      fun k  ->
        fun r  ->
          let rng =
            match r with
            | FStar_Pervasives_Native.Some r1 -> r1
            | FStar_Pervasives_Native.None  -> FStar_Range.dummyRange  in
          let i =
            let uu____3169 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____3169;
              FStar_Syntax_Syntax.lkind = k;
              FStar_Syntax_Syntax.ltyp = typ;
              FStar_Syntax_Syntax.rng = rng
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i)
            FStar_Pervasives_Native.None rng
  
let (canon_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____3182 =
      let uu____3197 = unascribe t  in head_and_args' uu____3197  in
    match uu____3182 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____3231 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____3242 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____3253 -> false
  
let (injectives : Prims.string Prims.list) =
  ["FStar.Int8.int_to_t";
  "FStar.Int16.int_to_t";
  "FStar.Int32.int_to_t";
  "FStar.Int64.int_to_t";
  "FStar.UInt8.uint_to_t";
  "FStar.UInt16.uint_to_t";
  "FStar.UInt32.uint_to_t";
  "FStar.UInt64.uint_to_t";
  "FStar.Int8.__int_to_t";
  "FStar.Int16.__int_to_t";
  "FStar.Int32.__int_to_t";
  "FStar.Int64.__int_to_t";
  "FStar.UInt8.__uint_to_t";
  "FStar.UInt16.__uint_to_t";
  "FStar.UInt32.__uint_to_t";
  "FStar.UInt64.__uint_to_t"] 
let (eq_inj : eq_result -> eq_result -> eq_result) =
  fun f  ->
    fun g  ->
      match (f, g) with
      | (Equal ,Equal ) -> Equal
      | (NotEqual ,uu____3303) -> NotEqual
      | (uu____3304,NotEqual ) -> NotEqual
      | (Unknown ,uu____3305) -> Unknown
      | (uu____3306,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___121_3427 = if uu___121_3427 then Equal else Unknown
         in
      let equal_iff uu___122_3438 = if uu___122_3438 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____3459 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3481 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3481
        then
          let uu____3485 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3562  ->
                    match uu____3562 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3603 = eq_tm a1 a2  in
                        eq_inj acc uu____3603) Equal) uu____3485
        else NotEqual  in
      let uu____3606 =
        let uu____3611 =
          let uu____3612 = unmeta t11  in uu____3612.FStar_Syntax_Syntax.n
           in
        let uu____3615 =
          let uu____3616 = unmeta t21  in uu____3616.FStar_Syntax_Syntax.n
           in
        (uu____3611, uu____3615)  in
      match uu____3606 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3622,uu____3623) ->
          let uu____3624 = unlazy t11  in eq_tm uu____3624 t21
      | (uu____3625,FStar_Syntax_Syntax.Tm_lazy uu____3626) ->
          let uu____3627 = unlazy t21  in eq_tm t11 uu____3627
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          if
            (f.FStar_Syntax_Syntax.fv_qual =
               (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
              &&
              (g.FStar_Syntax_Syntax.fv_qual =
                 (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
          then equal_data f [] g []
          else
            (let uu____3655 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____3655)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3669 = eq_tm f g  in
          eq_and uu____3669
            (fun uu____3672  ->
               let uu____3673 = eq_univs_list us vs  in equal_if uu____3673)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3675),uu____3676) -> Unknown
      | (uu____3677,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3678)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3681 = FStar_Const.eq_const c d  in equal_iff uu____3681
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3684)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3686))) ->
          let uu____3715 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3715
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3769 =
            let uu____3774 =
              let uu____3775 = un_uinst h1  in
              uu____3775.FStar_Syntax_Syntax.n  in
            let uu____3778 =
              let uu____3779 = un_uinst h2  in
              uu____3779.FStar_Syntax_Syntax.n  in
            (uu____3774, uu____3778)  in
          (match uu____3769 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (f1.FStar_Syntax_Syntax.fv_qual =
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
                 &&
                 (f2.FStar_Syntax_Syntax.fv_qual =
                    (FStar_Pervasives_Native.Some
                       FStar_Syntax_Syntax.Data_ctor))
               -> equal_data f1 args1 f2 args2
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3791 =
                    let uu____3793 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3793  in
                  FStar_List.mem uu____3791 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3795 ->
               let uu____3800 = eq_tm h1 h2  in
               eq_and uu____3800 (fun uu____3802  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3908 = FStar_List.zip bs1 bs2  in
            let uu____3971 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____4008  ->
                 fun a  ->
                   match uu____4008 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4101  -> branch_matches b1 b2))
              uu____3908 uu____3971
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____4106 = eq_univs u v1  in equal_if uu____4106
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____4120 = eq_quoteinfo q1 q2  in
          eq_and uu____4120 (fun uu____4122  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____4135 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4135 (fun uu____4137  -> eq_tm phi1 phi2)
      | uu____4138 -> Unknown

and (eq_quoteinfo :
  FStar_Syntax_Syntax.quoteinfo -> FStar_Syntax_Syntax.quoteinfo -> eq_result)
  =
  fun q1  ->
    fun q2  ->
      if q1.FStar_Syntax_Syntax.qkind <> q2.FStar_Syntax_Syntax.qkind
      then NotEqual
      else
        eq_antiquotes q1.FStar_Syntax_Syntax.antiquotes
          q2.FStar_Syntax_Syntax.antiquotes

and (eq_antiquotes :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                            FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                              FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 Prims.list -> eq_result)
  =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ([],uu____4210) -> NotEqual
      | (uu____4241,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____4333 = eq_tm t1 t2  in
             match uu____4333 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4334 = eq_antiquotes a11 a21  in
                 (match uu____4334 with
                  | NotEqual  -> NotEqual
                  | uu____4335 -> Unknown)
             | Equal  -> eq_antiquotes a11 a21)

and (eq_aqual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      eq_result)
  =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          Equal
      | (FStar_Pervasives_Native.None ,uu____4350) -> NotEqual
      | (uu____4357,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4387 -> NotEqual

and (branch_matches :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax
                                                             FStar_Pervasives_Native.option,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                               FStar_Syntax_Syntax.syntax
                                                               FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 -> eq_result)
  =
  fun b1  ->
    fun b2  ->
      let related_by f o1 o2 =
        match (o1, o2) with
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            true
        | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y) ->
            f x y
        | (uu____4479,uu____4480) -> false  in
      let uu____4490 = b1  in
      match uu____4490 with
      | (p1,w1,t1) ->
          let uu____4524 = b2  in
          (match uu____4524 with
           | (p2,w2,t2) ->
               let uu____4558 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4558
               then
                 let uu____4561 =
                   (let uu____4565 = eq_tm t1 t2  in uu____4565 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4574 = eq_tm t11 t21  in
                             uu____4574 = Equal) w1 w2)
                    in
                 (if uu____4561 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4639)::a11,(b,uu____4642)::b1) ->
          let uu____4716 = eq_tm a b  in
          (match uu____4716 with
           | Equal  -> eq_args a11 b1
           | uu____4717 -> Unknown)
      | uu____4718 -> Unknown

and (eq_univs_list :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool)
  =
  fun us  ->
    fun vs  ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)

let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4754) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4760,uu____4761) ->
        unrefine t2
    | uu____4802 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4810 =
      let uu____4811 = FStar_Syntax_Subst.compress t  in
      uu____4811.FStar_Syntax_Syntax.n  in
    match uu____4810 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4815 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4830) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4835 ->
        let uu____4852 =
          let uu____4853 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4853 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4852 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4916,uu____4917) ->
        is_uvar t1
    | uu____4958 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4967 =
      let uu____4968 = unrefine t  in uu____4968.FStar_Syntax_Syntax.n  in
    match uu____4967 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4974) -> is_unit t1
    | uu____4979 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4988 =
      let uu____4989 = FStar_Syntax_Subst.compress t  in
      uu____4989.FStar_Syntax_Syntax.n  in
    match uu____4988 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____4994 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5003 =
      let uu____5004 = unrefine t  in uu____5004.FStar_Syntax_Syntax.n  in
    match uu____5003 with
    | FStar_Syntax_Syntax.Tm_type uu____5008 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____5012) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5038) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____5043,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____5065 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5074 =
      let uu____5075 = FStar_Syntax_Subst.compress e  in
      uu____5075.FStar_Syntax_Syntax.n  in
    match uu____5074 with
    | FStar_Syntax_Syntax.Tm_abs uu____5079 -> true
    | uu____5099 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5108 =
      let uu____5109 = FStar_Syntax_Subst.compress t  in
      uu____5109.FStar_Syntax_Syntax.n  in
    match uu____5108 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5113 -> true
    | uu____5129 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5139) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5145,uu____5146) ->
        pre_typ t2
    | uu____5187 -> t1
  
let (destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                              FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ  in
      let uu____5212 =
        let uu____5213 = un_uinst typ1  in uu____5213.FStar_Syntax_Syntax.n
         in
      match uu____5212 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5278 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5308 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5329,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5336) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5341,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5352,uu____5353,uu____5354,uu____5355,uu____5356) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5366,uu____5367,uu____5368,uu____5369) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5375,uu____5376,uu____5377,uu____5378,uu____5379) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5387,uu____5388) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5390,uu____5391) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5394 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5395 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5396 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5410 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___123_5436  ->
    match uu___123_5436 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5450 'Auu____5451 .
    ('Auu____5450 FStar_Syntax_Syntax.syntax,'Auu____5451)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____5462  ->
    match uu____5462 with | (hd1,uu____5470) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5484 'Auu____5485 .
    ('Auu____5484 FStar_Syntax_Syntax.syntax,'Auu____5485)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range -> FStar_Range.range
  =
  fun args  ->
    fun r  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left
           (fun r1  -> fun a  -> FStar_Range.union_ranges r1 (range_of_arg a))
           r)
  
let (mk_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____5583 ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args))
            FStar_Pervasives_Native.None r
  
let (mk_app_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun bs  ->
      let uu____5642 =
        FStar_List.map
          (fun uu____5669  ->
             match uu____5669 with
             | (bv,aq) ->
                 let uu____5688 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5688, aq)) bs
         in
      mk_app f uu____5642
  
let (mk_data :
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Syntax_Syntax.syntax)
  =
  fun l  ->
    fun args  ->
      match args with
      | [] ->
          let uu____5738 = FStar_Ident.range_of_lid l  in
          let uu____5739 =
            let uu____5748 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5748  in
          uu____5739 FStar_Pervasives_Native.None uu____5738
      | uu____5756 ->
          let e =
            let uu____5770 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5770 args  in
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
  
let (field_projector_prefix : Prims.string) = "__proj__" 
let (field_projector_sep : Prims.string) = "__item__" 
let (field_projector_contains_constructor : Prims.string -> Prims.bool) =
  fun s  -> FStar_Util.starts_with s field_projector_prefix 
let (mk_field_projector_name_from_string :
  Prims.string -> Prims.string -> Prims.string) =
  fun constr  ->
    fun field  ->
      Prims.strcat field_projector_prefix
        (Prims.strcat constr (Prims.strcat field_projector_sep field))
  
let (mk_field_projector_name_from_ident :
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun lid  ->
    fun i  ->
      let itext = i.FStar_Ident.idText  in
      let newi =
        if field_projector_contains_constructor itext
        then i
        else
          FStar_Ident.mk_ident
            ((mk_field_projector_name_from_string
                (lid.FStar_Ident.ident).FStar_Ident.idText itext),
              (i.FStar_Ident.idRange))
         in
      FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns [newi])
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv ->
      Prims.int ->
        (FStar_Ident.lident,FStar_Syntax_Syntax.bv)
          FStar_Pervasives_Native.tuple2)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5847 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5847
          then
            let uu____5850 =
              let uu____5856 =
                let uu____5858 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____5858  in
              let uu____5861 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5856, uu____5861)  in
            FStar_Ident.mk_ident uu____5850
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___130_5866 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___130_5866.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___130_5866.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5867 = mk_field_projector_name_from_ident lid nm  in
        (uu____5867, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5879) -> ses
    | uu____5888 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____5899 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5912 = FStar_Syntax_Unionfind.find uv  in
      match uu____5912 with
      | FStar_Pervasives_Native.Some uu____5915 ->
          let uu____5916 =
            let uu____5918 =
              let uu____5920 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5920  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5918  in
          failwith uu____5916
      | uu____5925 -> FStar_Syntax_Unionfind.change uv t
  
let (qualifier_equal :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun q1  ->
    fun q2  ->
      match (q1, q2) with
      | (FStar_Syntax_Syntax.Discriminator
         l1,FStar_Syntax_Syntax.Discriminator l2) ->
          FStar_Ident.lid_equals l1 l2
      | (FStar_Syntax_Syntax.Projector
         (l1a,l1b),FStar_Syntax_Syntax.Projector (l2a,l2b)) ->
          (FStar_Ident.lid_equals l1a l2a) &&
            (l1b.FStar_Ident.idText = l2b.FStar_Ident.idText)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
                 f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
               f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
                 f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
               f1 f2)
      | uu____6008 -> q1 = q2
  
let (abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        let close_lopt lopt1 =
          match lopt1 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rc ->
              let uu____6054 =
                let uu___131_6055 = rc  in
                let uu____6056 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___131_6055.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6056;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___131_6055.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6054
           in
        match bs with
        | [] -> t
        | uu____6073 ->
            let body =
              let uu____6075 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6075  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6105 =
                   let uu____6112 =
                     let uu____6113 =
                       let uu____6132 =
                         let uu____6141 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6141 bs'  in
                       let uu____6156 = close_lopt lopt'  in
                       (uu____6132, t1, uu____6156)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6113  in
                   FStar_Syntax_Syntax.mk uu____6112  in
                 uu____6105 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6174 ->
                 let uu____6175 =
                   let uu____6182 =
                     let uu____6183 =
                       let uu____6202 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6211 = close_lopt lopt  in
                       (uu____6202, body, uu____6211)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6183  in
                   FStar_Syntax_Syntax.mk uu____6182  in
                 uu____6175 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos)
  
let (arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____6270 ->
          let uu____6279 =
            let uu____6286 =
              let uu____6287 =
                let uu____6302 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6311 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6302, uu____6311)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6287  in
            FStar_Syntax_Syntax.mk uu____6286  in
          uu____6279 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6363 =
        let uu____6364 = FStar_Syntax_Subst.compress t  in
        uu____6364.FStar_Syntax_Syntax.n  in
      match uu____6363 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6394) ->
               let uu____6403 =
                 let uu____6404 = FStar_Syntax_Subst.compress tres  in
                 uu____6404.FStar_Syntax_Syntax.n  in
               (match uu____6403 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6447 -> t)
           | uu____6448 -> t)
      | uu____6449 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6467 =
        let uu____6468 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6468 t.FStar_Syntax_Syntax.pos  in
      let uu____6469 =
        let uu____6476 =
          let uu____6477 =
            let uu____6484 =
              let uu____6487 =
                let uu____6488 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6488]  in
              FStar_Syntax_Subst.close uu____6487 t  in
            (b, uu____6484)  in
          FStar_Syntax_Syntax.Tm_refine uu____6477  in
        FStar_Syntax_Syntax.mk uu____6476  in
      uu____6469 FStar_Pervasives_Native.None uu____6467
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                               FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____6571 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6571 with
         | (bs1,c1) ->
             let uu____6590 = is_total_comp c1  in
             if uu____6590
             then
               let uu____6605 = arrow_formals_comp (comp_result c1)  in
               (match uu____6605 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6672;
           FStar_Syntax_Syntax.index = uu____6673;
           FStar_Syntax_Syntax.sort = s;_},uu____6675)
        ->
        let rec aux s1 k2 =
          let uu____6706 =
            let uu____6707 = FStar_Syntax_Subst.compress s1  in
            uu____6707.FStar_Syntax_Syntax.n  in
          match uu____6706 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6722 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6737;
                 FStar_Syntax_Syntax.index = uu____6738;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6740)
              -> aux s2 k2
          | uu____6748 ->
              let uu____6749 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6749)
           in
        aux s k1
    | uu____6764 ->
        let uu____6765 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6765)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                               FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____6800 = arrow_formals_comp k  in
    match uu____6800 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int,Prims.bool Prims.list FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6942 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6942 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6966 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___124_6975  ->
                         match uu___124_6975 with
                         | FStar_Syntax_Syntax.DECREASES uu____6977 -> true
                         | uu____6981 -> false))
                  in
               (match uu____6966 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7016 ->
                    let uu____7019 = is_total_comp c1  in
                    if uu____7019
                    then
                      let uu____7038 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7038 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7131;
             FStar_Syntax_Syntax.index = uu____7132;
             FStar_Syntax_Syntax.sort = k2;_},uu____7134)
          -> arrow_until_decreases k2
      | uu____7142 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7163 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7163 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7217 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7238 =
                 FStar_Common.tabulate n_univs (fun uu____7248  -> false)  in
               let uu____7251 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7276  ->
                         match uu____7276 with
                         | (x,uu____7285) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7238 uu____7251)
           in
        ((n_univs + (FStar_List.length bs)), uu____7217)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.residual_comp
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3)
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7347 =
            let uu___132_7348 = rc  in
            let uu____7349 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___132_7348.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7349;
              FStar_Syntax_Syntax.residual_flags =
                (uu___132_7348.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7347
      | uu____7358 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7392 =
        let uu____7393 =
          let uu____7396 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7396  in
        uu____7393.FStar_Syntax_Syntax.n  in
      match uu____7392 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7442 = aux t2 what  in
          (match uu____7442 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7514 -> ([], t1, abs_body_lcomp)  in
    let uu____7531 = aux t FStar_Pervasives_Native.None  in
    match uu____7531 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7579 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7579 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (mk_letbinding :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
              -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
  =
  fun lbname  ->
    fun univ_vars  ->
      fun typ  ->
        fun eff  ->
          fun def  ->
            fun lbattrs  ->
              fun pos  ->
                {
                  FStar_Syntax_Syntax.lbname = lbname;
                  FStar_Syntax_Syntax.lbunivs = univ_vars;
                  FStar_Syntax_Syntax.lbtyp = typ;
                  FStar_Syntax_Syntax.lbeff = eff;
                  FStar_Syntax_Syntax.lbdef = def;
                  FStar_Syntax_Syntax.lbattrs = lbattrs;
                  FStar_Syntax_Syntax.lbpos = pos
                }
  
let (close_univs_and_mk_letbinding :
  FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
                -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
  =
  fun recs  ->
    fun lbname  ->
      fun univ_vars  ->
        fun typ  ->
          fun eff  ->
            fun def  ->
              fun attrs  ->
                fun pos  ->
                  let def1 =
                    match (recs, univ_vars) with
                    | (FStar_Pervasives_Native.None ,uu____7742) -> def
                    | (uu____7753,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7765) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _0_1  -> FStar_Syntax_Syntax.U_name _0_1))
                           in
                        let inst1 =
                          FStar_All.pipe_right fvs
                            (FStar_List.map
                               (fun fv  ->
                                  (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                    universes)))
                           in
                        FStar_Syntax_InstFV.instantiate inst1 def
                     in
                  let typ1 = FStar_Syntax_Subst.close_univ_vars univ_vars typ
                     in
                  let def2 =
                    FStar_Syntax_Subst.close_univ_vars univ_vars def1  in
                  mk_letbinding lbname univ_vars typ1 eff def2 attrs pos
  
let (open_univ_vars_binders_and_comp :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                                  FStar_Pervasives_Native.option)
                                          FStar_Pervasives_Native.tuple2
                                          Prims.list,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple3)
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____7862 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7862 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7897 ->
            let t' = arrow binders c  in
            let uu____7909 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____7909 with
             | (uvs1,t'1) ->
                 let uu____7930 =
                   let uu____7931 = FStar_Syntax_Subst.compress t'1  in
                   uu____7931.FStar_Syntax_Syntax.n  in
                 (match uu____7930 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____7980 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____8005 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8016 -> false
  
let (is_lid_equality : FStar_Ident.lident -> Prims.bool) =
  fun x  -> FStar_Ident.lid_equals x FStar_Parser_Const.eq2_lid 
let (is_forall : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.forall_lid 
let (is_exists : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.exists_lid 
let (is_qlid : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> (is_forall lid) || (is_exists lid) 
let (is_equality :
  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun x  -> is_lid_equality x.FStar_Syntax_Syntax.v 
let (lid_is_connective : FStar_Ident.lident -> Prims.bool) =
  let lst =
    [FStar_Parser_Const.and_lid;
    FStar_Parser_Const.or_lid;
    FStar_Parser_Const.not_lid;
    FStar_Parser_Const.iff_lid;
    FStar_Parser_Const.imp_lid]  in
  fun lid  -> FStar_Util.for_some (FStar_Ident.lid_equals lid) lst 
let (is_constructor :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8079 =
        let uu____8080 = pre_typ t  in uu____8080.FStar_Syntax_Syntax.n  in
      match uu____8079 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8085 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8099 =
        let uu____8100 = pre_typ t  in uu____8100.FStar_Syntax_Syntax.n  in
      match uu____8099 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8104 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8106) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8132) ->
          is_constructed_typ t1 lid
      | uu____8137 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8150 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8151 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8152 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8154) -> get_tycon t2
    | uu____8179 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8187 =
      let uu____8188 = un_uinst t  in uu____8188.FStar_Syntax_Syntax.n  in
    match uu____8187 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8193 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____8207 =
        let uu____8211 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____8211  in
      match uu____8207 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8243 -> false
    else false
  
let (ktype : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (ktype0 : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (type_u :
  unit ->
    (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____8262  ->
    let u =
      let uu____8268 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_2  -> FStar_Syntax_Syntax.U_unif _0_2)
        uu____8268
       in
    let uu____8285 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8285, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8298 = eq_tm a a'  in
      match uu____8298 with | Equal  -> true | uu____8301 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8306 =
    let uu____8313 =
      let uu____8314 =
        let uu____8315 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8315
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8314  in
    FStar_Syntax_Syntax.mk uu____8313  in
  uu____8306 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (exp_true_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_false_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_unit : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_int : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_int (s, FStar_Pervasives_Native.None)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_char : FStar_BaseTypes.char -> FStar_Syntax_Syntax.term) =
  fun c  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_string : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (s, FStar_Range.dummyRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (fvar_const : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
      FStar_Pervasives_Native.None
  
let (tand : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.and_lid 
let (tor : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.or_lid 
let (timp : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (tiff : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "2"))
    FStar_Pervasives_Native.None
  
let (t_bool : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.bool_lid 
let (b2t_v : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.b2t_lid 
let (t_not : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.not_lid 
let (t_false : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.false_lid 
let (t_true : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.true_lid 
let (tac_opaque_attr : FStar_Syntax_Syntax.term) = exp_string "tac_opaque" 
let (dm4f_bind_range_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.dm4f_bind_range_attr 
let (tcdecltime_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.tcdecltime_attr 
let (inline_let_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.inline_let_attr 
let (t_ctx_uvar_and_sust : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.ctx_uvar_and_subst_lid 
let (mk_conj_opt :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu____8429 =
            let uu____8432 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8433 =
              let uu____8440 =
                let uu____8441 =
                  let uu____8458 =
                    let uu____8469 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8478 =
                      let uu____8489 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8489]  in
                    uu____8469 :: uu____8478  in
                  (tand, uu____8458)  in
                FStar_Syntax_Syntax.Tm_app uu____8441  in
              FStar_Syntax_Syntax.mk uu____8440  in
            uu____8433 FStar_Pervasives_Native.None uu____8432  in
          FStar_Pervasives_Native.Some uu____8429
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8569 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8570 =
          let uu____8577 =
            let uu____8578 =
              let uu____8595 =
                let uu____8606 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8615 =
                  let uu____8626 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8626]  in
                uu____8606 :: uu____8615  in
              (op_t, uu____8595)  in
            FStar_Syntax_Syntax.Tm_app uu____8578  in
          FStar_Syntax_Syntax.mk uu____8577  in
        uu____8570 FStar_Pervasives_Native.None uu____8569
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8686 =
      let uu____8693 =
        let uu____8694 =
          let uu____8711 =
            let uu____8722 = FStar_Syntax_Syntax.as_arg phi  in [uu____8722]
             in
          (t_not, uu____8711)  in
        FStar_Syntax_Syntax.Tm_app uu____8694  in
      FStar_Syntax_Syntax.mk uu____8693  in
    uu____8686 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
let (mk_conj :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tand phi1 phi2 
let (mk_conj_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
  
let (mk_disj :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tor phi1 phi2 
let (mk_disj_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
  
let (mk_imp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop timp phi1 phi2 
let (mk_iff :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop tiff phi1 phi2 
let (b2t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e  ->
    let uu____8922 =
      let uu____8929 =
        let uu____8930 =
          let uu____8947 =
            let uu____8958 = FStar_Syntax_Syntax.as_arg e  in [uu____8958]
             in
          (b2t_v, uu____8947)  in
        FStar_Syntax_Syntax.Tm_app uu____8930  in
      FStar_Syntax_Syntax.mk uu____8929  in
    uu____8922 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9005 =
      let uu____9006 = unmeta t  in uu____9006.FStar_Syntax_Syntax.n  in
    match uu____9005 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9011 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9034 = is_t_true t1  in
      if uu____9034
      then t2
      else
        (let uu____9041 = is_t_true t2  in
         if uu____9041 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9069 = is_t_true t1  in
      if uu____9069
      then t_true
      else
        (let uu____9076 = is_t_true t2  in
         if uu____9076 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9105 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9106 =
        let uu____9113 =
          let uu____9114 =
            let uu____9131 =
              let uu____9142 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9151 =
                let uu____9162 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9162]  in
              uu____9142 :: uu____9151  in
            (teq, uu____9131)  in
          FStar_Syntax_Syntax.Tm_app uu____9114  in
        FStar_Syntax_Syntax.mk uu____9113  in
      uu____9106 FStar_Pervasives_Native.None uu____9105
  
let (mk_eq2 :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun u  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          let eq_inst = FStar_Syntax_Syntax.mk_Tm_uinst teq [u]  in
          let uu____9232 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9233 =
            let uu____9240 =
              let uu____9241 =
                let uu____9258 =
                  let uu____9269 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9278 =
                    let uu____9289 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9298 =
                      let uu____9309 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9309]  in
                    uu____9289 :: uu____9298  in
                  uu____9269 :: uu____9278  in
                (eq_inst, uu____9258)  in
              FStar_Syntax_Syntax.Tm_app uu____9241  in
            FStar_Syntax_Syntax.mk uu____9240  in
          uu____9233 FStar_Pervasives_Native.None uu____9232
  
let (mk_has_type :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun x  ->
      fun t'  ->
        let t_has_type = fvar_const FStar_Parser_Const.has_type_lid  in
        let t_has_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst
               (t_has_type,
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        let uu____9389 =
          let uu____9396 =
            let uu____9397 =
              let uu____9414 =
                let uu____9425 = FStar_Syntax_Syntax.iarg t  in
                let uu____9434 =
                  let uu____9445 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9454 =
                    let uu____9465 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9465]  in
                  uu____9445 :: uu____9454  in
                uu____9425 :: uu____9434  in
              (t_has_type1, uu____9414)  in
            FStar_Syntax_Syntax.Tm_app uu____9397  in
          FStar_Syntax_Syntax.mk uu____9396  in
        uu____9389 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (mk_with_type :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun t  ->
      fun e  ->
        let t_with_type =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        let t_with_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst (t_with_type, [u]))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        let uu____9545 =
          let uu____9552 =
            let uu____9553 =
              let uu____9570 =
                let uu____9581 = FStar_Syntax_Syntax.iarg t  in
                let uu____9590 =
                  let uu____9601 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9601]  in
                uu____9581 :: uu____9590  in
              (t_with_type1, uu____9570)  in
            FStar_Syntax_Syntax.Tm_app uu____9553  in
          FStar_Syntax_Syntax.mk uu____9552  in
        uu____9545 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9651 =
    let uu____9658 =
      let uu____9659 =
        let uu____9666 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9666, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9659  in
    FStar_Syntax_Syntax.mk uu____9658  in
  uu____9651 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (lex_pair : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (tforall : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (t_haseq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
  
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.lcomp) =
  fun c0  ->
    let uu____9684 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____9697 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____9708 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____9684 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____9729  -> c0)
  
let (mk_residual_comp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.cflag Prims.list ->
        FStar_Syntax_Syntax.residual_comp)
  =
  fun l  ->
    fun t  ->
      fun f  ->
        {
          FStar_Syntax_Syntax.residual_effect = l;
          FStar_Syntax_Syntax.residual_typ = t;
          FStar_Syntax_Syntax.residual_flags = f
        }
  
let (residual_tot :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.residual_comp)
  =
  fun t  ->
    {
      FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid;
      FStar_Syntax_Syntax.residual_typ = (FStar_Pervasives_Native.Some t);
      FStar_Syntax_Syntax.residual_flags = [FStar_Syntax_Syntax.TOTAL]
    }
  
let (residual_comp_of_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.residual_comp) =
  fun c  ->
    {
      FStar_Syntax_Syntax.residual_effect = (comp_effect_name c);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (comp_result c));
      FStar_Syntax_Syntax.residual_flags = (comp_flags c)
    }
  
let (residual_comp_of_lcomp :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.residual_comp) =
  fun lc  ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.FStar_Syntax_Syntax.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.FStar_Syntax_Syntax.cflags)
    }
  
let (mk_forall_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fa  ->
    fun x  ->
      fun body  ->
        let uu____9812 =
          let uu____9819 =
            let uu____9820 =
              let uu____9837 =
                let uu____9848 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____9857 =
                  let uu____9868 =
                    let uu____9877 =
                      let uu____9878 =
                        let uu____9879 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____9879]  in
                      abs uu____9878 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____9877  in
                  [uu____9868]  in
                uu____9848 :: uu____9857  in
              (fa, uu____9837)  in
            FStar_Syntax_Syntax.Tm_app uu____9820  in
          FStar_Syntax_Syntax.mk uu____9819  in
        uu____9812 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (mk_forall_no_univ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  = fun x  -> fun body  -> mk_forall_aux tforall x body 
let (mk_forall :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun u  ->
    fun x  ->
      fun body  ->
        let tforall1 = FStar_Syntax_Syntax.mk_Tm_uinst tforall [u]  in
        mk_forall_aux tforall1 x body
  
let (close_forall_no_univs :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____10009 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10009
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10028 -> true
    | uu____10030 -> false
  
let (if_then_else :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t1  ->
      fun t2  ->
        let then_branch =
          let uu____10077 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10077, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10106 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10106, FStar_Pervasives_Native.None, t2)  in
        let uu____10120 =
          let uu____10121 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10121  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10120
  
let (mk_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "1"))
          FStar_Pervasives_Native.None
         in
      let uu____10197 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10200 =
        let uu____10211 = FStar_Syntax_Syntax.as_arg p  in [uu____10211]  in
      mk_app uu____10197 uu____10200
  
let (mk_auto_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "2"))
          FStar_Pervasives_Native.None
         in
      let uu____10251 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10254 =
        let uu____10265 = FStar_Syntax_Syntax.as_arg p  in [uu____10265]  in
      mk_app uu____10251 uu____10254
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10300 = head_and_args t  in
    match uu____10300 with
    | (head1,args) ->
        let uu____10347 =
          let uu____10362 =
            let uu____10363 = un_uinst head1  in
            uu____10363.FStar_Syntax_Syntax.n  in
          (uu____10362, args)  in
        (match uu____10347 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10382)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10448 =
                    let uu____10453 =
                      let uu____10454 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10454]  in
                    FStar_Syntax_Subst.open_term uu____10453 p  in
                  (match uu____10448 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10511 -> failwith "impossible"  in
                       let uu____10519 =
                         let uu____10521 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10521
                          in
                       if uu____10519
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10537 -> FStar_Pervasives_Native.None)
         | uu____10540 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10571 = head_and_args t  in
    match uu____10571 with
    | (head1,args) ->
        let uu____10622 =
          let uu____10637 =
            let uu____10638 = FStar_Syntax_Subst.compress head1  in
            uu____10638.FStar_Syntax_Syntax.n  in
          (uu____10637, args)  in
        (match uu____10622 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10660;
               FStar_Syntax_Syntax.vars = uu____10661;_},u::[]),(t1,uu____10664)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10711 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10746 = head_and_args t  in
    match uu____10746 with
    | (head1,args) ->
        let uu____10797 =
          let uu____10812 =
            let uu____10813 = FStar_Syntax_Subst.compress head1  in
            uu____10813.FStar_Syntax_Syntax.n  in
          (uu____10812, args)  in
        (match uu____10797 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10835;
               FStar_Syntax_Syntax.vars = uu____10836;_},u::[]),(t1,uu____10839)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10886 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____10914 =
      let uu____10931 = unmeta t  in head_and_args uu____10931  in
    match uu____10914 with
    | (head1,uu____10934) ->
        let uu____10959 =
          let uu____10960 = un_uinst head1  in
          uu____10960.FStar_Syntax_Syntax.n  in
        (match uu____10959 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             (((((((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.squash_lid)
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.auto_squash_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.and_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.or_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.not_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.imp_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.iff_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.ite_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.exists_lid))
                       ||
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.forall_lid))
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.true_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.false_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq3_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.b2t_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.haseq_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.precedes_lid)
         | uu____10965 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10985 =
      let uu____10998 =
        let uu____10999 = FStar_Syntax_Subst.compress t  in
        uu____10999.FStar_Syntax_Syntax.n  in
      match uu____10998 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____11129 =
            let uu____11140 =
              let uu____11141 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____11141  in
            (b, uu____11140)  in
          FStar_Pervasives_Native.Some uu____11129
      | uu____11158 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____10985
      (fun uu____11196  ->
         match uu____11196 with
         | (b,c) ->
             let uu____11233 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11233 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11296 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11333 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11333
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3 
  | QEx of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3 
  | BaseConn of (FStar_Ident.lident,FStar_Syntax_Syntax.args)
  FStar_Pervasives_Native.tuple2 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11385 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11429 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11471 -> false
  
let (__proj__BaseConn__item___0 :
  connective ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | BaseConn _0 -> _0 
let (destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1  in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11511) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11523) ->
          unmeta_monadic t
      | uu____11536 -> f2  in
    let destruct_base_conn f1 =
      let connectives =
        [(FStar_Parser_Const.true_lid, (Prims.parse_int "0"));
        (FStar_Parser_Const.false_lid, (Prims.parse_int "0"));
        (FStar_Parser_Const.and_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.or_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.imp_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.iff_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.ite_lid, (Prims.parse_int "3"));
        (FStar_Parser_Const.not_lid, (Prims.parse_int "1"));
        (FStar_Parser_Const.eq2_lid, (Prims.parse_int "3"));
        (FStar_Parser_Const.eq2_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.eq3_lid, (Prims.parse_int "4"));
        (FStar_Parser_Const.eq3_lid, (Prims.parse_int "2"))]  in
      let aux f2 uu____11632 =
        match uu____11632 with
        | (lid,arity) ->
            let uu____11641 =
              let uu____11658 = unmeta_monadic f2  in
              head_and_args uu____11658  in
            (match uu____11641 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____11688 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____11688
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____11768 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____11768)
      | uu____11781 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____11848 = head_and_args t1  in
        match uu____11848 with
        | (t2,args) ->
            let uu____11903 = un_uinst t2  in
            let uu____11904 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____11945  ->
                      match uu____11945 with
                      | (t3,imp) ->
                          let uu____11964 = unascribe t3  in
                          (uu____11964, imp)))
               in
            (uu____11903, uu____11904)
         in
      let rec aux qopt out t1 =
        let uu____12015 = let uu____12039 = flat t1  in (qopt, uu____12039)
           in
        match uu____12015 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12079;
                 FStar_Syntax_Syntax.vars = uu____12080;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12083);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12084;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12085;_},uu____12086)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12188;
                 FStar_Syntax_Syntax.vars = uu____12189;_},uu____12190::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12193);
                  FStar_Syntax_Syntax.pos = uu____12194;
                  FStar_Syntax_Syntax.vars = uu____12195;_},uu____12196)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12313;
               FStar_Syntax_Syntax.vars = uu____12314;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12317);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12318;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12319;_},uu____12320)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12413 =
              let uu____12417 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12417  in
            aux uu____12413 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12427;
               FStar_Syntax_Syntax.vars = uu____12428;_},uu____12429::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12432);
                FStar_Syntax_Syntax.pos = uu____12433;
                FStar_Syntax_Syntax.vars = uu____12434;_},uu____12435)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12544 =
              let uu____12548 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12548  in
            aux uu____12544 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____12558) ->
            let bs = FStar_List.rev out  in
            let uu____12611 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____12611 with
             | (bs1,t2) ->
                 let uu____12620 = patterns t2  in
                 (match uu____12620 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____12670 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let u_connectives =
      [(FStar_Parser_Const.true_lid, FStar_Parser_Const.c_true_lid,
         (Prims.parse_int "0"));
      (FStar_Parser_Const.false_lid, FStar_Parser_Const.c_false_lid,
        (Prims.parse_int "0"));
      (FStar_Parser_Const.and_lid, FStar_Parser_Const.c_and_lid,
        (Prims.parse_int "2"));
      (FStar_Parser_Const.or_lid, FStar_Parser_Const.c_or_lid,
        (Prims.parse_int "2"))]
       in
    let destruct_sq_base_conn t =
      let uu____12762 = un_squash t  in
      FStar_Util.bind_opt uu____12762
        (fun t1  ->
           let uu____12778 = head_and_args' t1  in
           match uu____12778 with
           | (hd1,args) ->
               let uu____12817 =
                 let uu____12823 =
                   let uu____12824 = un_uinst hd1  in
                   uu____12824.FStar_Syntax_Syntax.n  in
                 (uu____12823, (FStar_List.length args))  in
               (match uu____12817 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_3) when
                    (_0_3 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_4) when
                    (_0_4 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_5) when
                    (_0_5 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_6) when
                    (_0_6 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_7) when
                    (_0_7 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_8) when
                    (_0_8 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_9) when
                    (_0_9 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_10) when
                    (_0_10 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____12854 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____12884 = un_squash t  in
      FStar_Util.bind_opt uu____12884
        (fun t1  ->
           let uu____12899 = arrow_one t1  in
           match uu____12899 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____12914 =
                 let uu____12916 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____12916  in
               if uu____12914
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____12926 = comp_to_comp_typ_nouniv c  in
                    uu____12926.FStar_Syntax_Syntax.result_typ  in
                  let uu____12927 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____12927
                  then
                    let uu____12934 = patterns q  in
                    match uu____12934 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____12997 =
                       let uu____12998 =
                         let uu____13003 =
                           let uu____13004 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13015 =
                             let uu____13026 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13026]  in
                           uu____13004 :: uu____13015  in
                         (FStar_Parser_Const.imp_lid, uu____13003)  in
                       BaseConn uu____12998  in
                     FStar_Pervasives_Native.Some uu____12997))
           | uu____13059 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13067 = un_squash t  in
      FStar_Util.bind_opt uu____13067
        (fun t1  ->
           let uu____13098 = head_and_args' t1  in
           match uu____13098 with
           | (hd1,args) ->
               let uu____13137 =
                 let uu____13152 =
                   let uu____13153 = un_uinst hd1  in
                   uu____13153.FStar_Syntax_Syntax.n  in
                 (uu____13152, args)  in
               (match uu____13137 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13170)::(a2,uu____13172)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13223 =
                      let uu____13224 = FStar_Syntax_Subst.compress a2  in
                      uu____13224.FStar_Syntax_Syntax.n  in
                    (match uu____13223 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13231) ->
                         let uu____13266 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13266 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13319 -> failwith "impossible"  in
                              let uu____13327 = patterns q1  in
                              (match uu____13327 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13388 -> FStar_Pervasives_Native.None)
                | uu____13389 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13412 = destruct_sq_forall phi  in
          (match uu____13412 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_11  -> FStar_Pervasives_Native.Some _0_11)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13428 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13434 = destruct_sq_exists phi  in
          (match uu____13434 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_12  -> FStar_Pervasives_Native.Some _0_12)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13450 -> f1)
      | uu____13453 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13457 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13457
      (fun uu____13462  ->
         let uu____13463 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13463
           (fun uu____13468  ->
              let uu____13469 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13469
                (fun uu____13474  ->
                   let uu____13475 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13475
                     (fun uu____13480  ->
                        let uu____13481 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13481
                          (fun uu____13485  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____13498 =
      let uu____13499 = FStar_Syntax_Subst.compress t  in
      uu____13499.FStar_Syntax_Syntax.n  in
    match uu____13498 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____13506) ->
        let uu____13541 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____13541 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____13575 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____13575
             then
               let uu____13582 =
                 let uu____13593 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____13593]  in
               mk_app t uu____13582
             else e1)
    | uu____13620 ->
        let uu____13621 =
          let uu____13632 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____13632]  in
        mk_app t uu____13621
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13674 =
            let uu____13679 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13679  in
          let uu____13680 =
            let uu____13681 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13681  in
          let uu____13684 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13674 a.FStar_Syntax_Syntax.action_univs uu____13680
            FStar_Parser_Const.effect_Tot_lid uu____13684 [] pos
           in
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_let
               ((false, [lb]), [a.FStar_Syntax_Syntax.action_name]));
          FStar_Syntax_Syntax.sigrng =
            ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.sigquals =
            [FStar_Syntax_Syntax.Visible_default;
            FStar_Syntax_Syntax.Action eff_lid];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta;
          FStar_Syntax_Syntax.sigattrs = []
        }
  
let (mk_reify :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reify_1 =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
       in
    let uu____13710 =
      let uu____13717 =
        let uu____13718 =
          let uu____13735 =
            let uu____13746 = FStar_Syntax_Syntax.as_arg t  in [uu____13746]
             in
          (reify_1, uu____13735)  in
        FStar_Syntax_Syntax.Tm_app uu____13718  in
      FStar_Syntax_Syntax.mk uu____13717  in
    uu____13710 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____13801 =
        let uu____13808 =
          let uu____13809 =
            let uu____13810 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____13810  in
          FStar_Syntax_Syntax.Tm_constant uu____13809  in
        FStar_Syntax_Syntax.mk uu____13808  in
      uu____13801 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____13815 =
      let uu____13822 =
        let uu____13823 =
          let uu____13840 =
            let uu____13851 = FStar_Syntax_Syntax.as_arg t  in [uu____13851]
             in
          (reflect_, uu____13840)  in
        FStar_Syntax_Syntax.Tm_app uu____13823  in
      FStar_Syntax_Syntax.mk uu____13822  in
    uu____13815 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13898 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____13923 = unfold_lazy i  in delta_qualifier uu____13923
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____13925 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____13926 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____13927 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____13950 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____13963 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____13964 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____13971 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____13972 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____13988) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____13993;
           FStar_Syntax_Syntax.index = uu____13994;
           FStar_Syntax_Syntax.sort = t2;_},uu____13996)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14005) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14011,uu____14012) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14054) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14079,t2,uu____14081) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14106,t2) -> delta_qualifier t2
  
let rec (incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth) =
  fun d  ->
    match d with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Syntax_Syntax.Delta_constant_at_level
          (i + (Prims.parse_int "1"))
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Syntax_Syntax.Delta_equational_at_level
          (i + (Prims.parse_int "1"))
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
  
let (incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let uu____14145 = delta_qualifier t  in incr_delta_depth uu____14145
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14153 =
      let uu____14154 = FStar_Syntax_Subst.compress t  in
      uu____14154.FStar_Syntax_Syntax.n  in
    match uu____14153 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14159 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____14175 =
      let uu____14192 = unmeta e  in head_and_args uu____14192  in
    match uu____14175 with
    | (head1,args) ->
        let uu____14223 =
          let uu____14238 =
            let uu____14239 = un_uinst head1  in
            uu____14239.FStar_Syntax_Syntax.n  in
          (uu____14238, args)  in
        (match uu____14223 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____14257) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____14281::(hd1,uu____14283)::(tl1,uu____14285)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____14352 =
               let uu____14355 =
                 let uu____14358 = list_elements tl1  in
                 FStar_Util.must uu____14358  in
               hd1 :: uu____14355  in
             FStar_Pervasives_Native.Some uu____14352
         | uu____14367 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____14391 .
    ('Auu____14391 -> 'Auu____14391) ->
      'Auu____14391 Prims.list -> 'Auu____14391 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14417 = f a  in [uu____14417]
      | x::xs -> let uu____14422 = apply_last f xs  in x :: uu____14422
  
let (dm4f_lid :
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident) =
  fun ed  ->
    fun name  ->
      let p = FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname  in
      let p' =
        apply_last
          (fun s  ->
             Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))
          p
         in
      FStar_Ident.lid_of_path p' FStar_Range.dummyRange
  
let rec (mk_list :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term)
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____14477 =
            let uu____14484 =
              let uu____14485 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14485  in
            FStar_Syntax_Syntax.mk uu____14484  in
          uu____14477 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____14502 =
            let uu____14507 =
              let uu____14508 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14508
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14507 args  in
          uu____14502 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14524 =
            let uu____14529 =
              let uu____14530 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14530
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14529 args  in
          uu____14524 FStar_Pervasives_Native.None pos  in
        let uu____14533 =
          let uu____14534 =
            let uu____14535 = FStar_Syntax_Syntax.iarg typ  in [uu____14535]
             in
          nil uu____14534 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14569 =
                 let uu____14570 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14579 =
                   let uu____14590 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14599 =
                     let uu____14610 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14610]  in
                   uu____14590 :: uu____14599  in
                 uu____14570 :: uu____14579  in
               cons1 uu____14569 t.FStar_Syntax_Syntax.pos) l uu____14533
  
let rec eqlist :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq1  ->
    fun xs  ->
      fun ys  ->
        match (xs, ys) with
        | ([],[]) -> true
        | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
        | uu____14719 -> false
  
let eqsum :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) ->
        ('a,'b) FStar_Util.either -> ('a,'b) FStar_Util.either -> Prims.bool
  =
  fun e1  ->
    fun e2  ->
      fun x  ->
        fun y  ->
          match (x, y) with
          | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
          | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
          | uu____14833 -> false
  
let eqprod :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) ->
        ('a,'b) FStar_Pervasives_Native.tuple2 ->
          ('a,'b) FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun e1  ->
    fun e2  ->
      fun x  ->
        fun y  ->
          match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
  
let eqopt :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a FStar_Pervasives_Native.option ->
        'a FStar_Pervasives_Native.option -> Prims.bool
  =
  fun e  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (FStar_Pervasives_Native.Some x1,FStar_Pervasives_Native.Some y1)
            -> e x1 y1
        | uu____14999 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15048 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15048
          then FStar_Util.print1 ">>> term_eq failing: %s\n" msg
          else ());
         false)
  
let (fail : Prims.string -> Prims.bool) = fun msg  -> check msg false 
let rec (term_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun dbg  ->
    fun t1  ->
      fun t2  ->
        let t11 = let uu____15270 = unmeta_safe t1  in canon_app uu____15270
           in
        let t21 = let uu____15276 = unmeta_safe t2  in canon_app uu____15276
           in
        let uu____15279 =
          let uu____15284 =
            let uu____15285 =
              let uu____15288 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15288  in
            uu____15285.FStar_Syntax_Syntax.n  in
          let uu____15289 =
            let uu____15290 =
              let uu____15293 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15293  in
            uu____15290.FStar_Syntax_Syntax.n  in
          (uu____15284, uu____15289)  in
        match uu____15279 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15295,uu____15296) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15305,FStar_Syntax_Syntax.Tm_uinst uu____15306) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15315,uu____15316) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15341,FStar_Syntax_Syntax.Tm_delayed uu____15342) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15367,uu____15368) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15397,FStar_Syntax_Syntax.Tm_ascribed uu____15398) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15437 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15437
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15442 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15442
        | (FStar_Syntax_Syntax.Tm_type
           uu____15445,FStar_Syntax_Syntax.Tm_type uu____15446) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15504 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15504) &&
              (let uu____15514 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15514)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15563 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15563) &&
              (let uu____15573 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15573)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____15591 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15591)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15648 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15648) &&
              (let uu____15652 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15652)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15741 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15741) &&
              (let uu____15745 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15745)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15762,uu____15763) ->
            let uu____15764 =
              let uu____15766 = unlazy t11  in
              term_eq_dbg dbg uu____15766 t21  in
            check "lazy_l" uu____15764
        | (uu____15768,FStar_Syntax_Syntax.Tm_lazy uu____15769) ->
            let uu____15770 =
              let uu____15772 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15772  in
            check "lazy_r" uu____15770
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15817 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15817))
              &&
              (let uu____15821 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15821)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15825),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15827)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15885 =
               let uu____15887 = eq_quoteinfo qi1 qi2  in uu____15887 = Equal
                in
             check "tm_quoted qi" uu____15885) &&
              (let uu____15890 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15890)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15920 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15920) &&
                   (let uu____15924 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15924)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15943 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15943) &&
                    (let uu____15947 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15947))
                   &&
                   (let uu____15951 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15951)
             | uu____15954 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15960) -> fail "unk"
        | (uu____15962,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15964,uu____15965) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15967,uu____15968) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15970,uu____15971) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15973,uu____15974) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15976,uu____15977) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15979,uu____15980) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____16000,uu____16001) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____16017,uu____16018) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____16026,uu____16027) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____16045,uu____16046) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16070,uu____16071) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16086,uu____16087) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16101,uu____16102) ->
            fail "bottom"
        | (uu____16110,FStar_Syntax_Syntax.Tm_bvar uu____16111) ->
            fail "bottom"
        | (uu____16113,FStar_Syntax_Syntax.Tm_name uu____16114) ->
            fail "bottom"
        | (uu____16116,FStar_Syntax_Syntax.Tm_fvar uu____16117) ->
            fail "bottom"
        | (uu____16119,FStar_Syntax_Syntax.Tm_constant uu____16120) ->
            fail "bottom"
        | (uu____16122,FStar_Syntax_Syntax.Tm_type uu____16123) ->
            fail "bottom"
        | (uu____16125,FStar_Syntax_Syntax.Tm_abs uu____16126) ->
            fail "bottom"
        | (uu____16146,FStar_Syntax_Syntax.Tm_arrow uu____16147) ->
            fail "bottom"
        | (uu____16163,FStar_Syntax_Syntax.Tm_refine uu____16164) ->
            fail "bottom"
        | (uu____16172,FStar_Syntax_Syntax.Tm_app uu____16173) ->
            fail "bottom"
        | (uu____16191,FStar_Syntax_Syntax.Tm_match uu____16192) ->
            fail "bottom"
        | (uu____16216,FStar_Syntax_Syntax.Tm_let uu____16217) ->
            fail "bottom"
        | (uu____16232,FStar_Syntax_Syntax.Tm_uvar uu____16233) ->
            fail "bottom"
        | (uu____16247,FStar_Syntax_Syntax.Tm_meta uu____16248) ->
            fail "bottom"

and (arg_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                              FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun dbg  ->
    fun a1  ->
      fun a2  ->
        eqprod
          (fun t1  ->
             fun t2  ->
               let uu____16283 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16283)
          (fun q1  ->
             fun q2  ->
               let uu____16295 =
                 let uu____16297 = eq_aqual q1 q2  in uu____16297 = Equal  in
               check "arg qual" uu____16295) a1 a2

and (binder_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun dbg  ->
    fun b1  ->
      fun b2  ->
        eqprod
          (fun b11  ->
             fun b21  ->
               let uu____16322 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16322)
          (fun q1  ->
             fun q2  ->
               let uu____16334 =
                 let uu____16336 = eq_aqual q1 q2  in uu____16336 = Equal  in
               check "binder qual" uu____16334) b1 b2

and (lcomp_eq_dbg :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c1  -> fun c2  -> fail "lcomp"

and (residual_eq_dbg :
  FStar_Syntax_Syntax.residual_comp ->
    FStar_Syntax_Syntax.residual_comp -> Prims.bool)
  = fun r1  -> fun r2  -> fail "residual"

and (comp_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun dbg  ->
    fun c1  ->
      fun c2  ->
        let c11 = comp_to_comp_typ_nouniv c1  in
        let c21 = comp_to_comp_typ_nouniv c2  in
        ((let uu____16356 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16356) &&
           (let uu____16360 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16360))
          && true

and (eq_flags_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.cflag -> FStar_Syntax_Syntax.cflag -> Prims.bool)
  = fun dbg  -> fun f1  -> fun f2  -> true

and (branch_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                               FStar_Syntax_Syntax.syntax
                                                               FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 -> Prims.bool)
  =
  fun dbg  ->
    fun uu____16370  ->
      fun uu____16371  ->
        match (uu____16370, uu____16371) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16498 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16498) &&
               (let uu____16502 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16502))
              &&
              (let uu____16506 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16548 -> false  in
               check "branch when" uu____16506)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16569 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16569) &&
           (let uu____16578 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16578))
          &&
          (let uu____16582 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16582)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16599 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16599 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16653 ->
        let uu____16676 =
          let uu____16678 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16678  in
        (Prims.parse_int "1") + uu____16676
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16681 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____16681
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16685 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____16685
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16694 = sizeof t1  in (FStar_List.length us) + uu____16694
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16698) ->
        let uu____16723 = sizeof t1  in
        let uu____16725 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16740  ->
                 match uu____16740 with
                 | (bv,uu____16750) ->
                     let uu____16755 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16755) (Prims.parse_int "0") bs
           in
        uu____16723 + uu____16725
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____16784 = sizeof hd1  in
        let uu____16786 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16801  ->
                 match uu____16801 with
                 | (arg,uu____16811) ->
                     let uu____16816 = sizeof arg  in acc + uu____16816)
            (Prims.parse_int "0") args
           in
        uu____16784 + uu____16786
    | uu____16819 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16833 =
        let uu____16834 = un_uinst t  in uu____16834.FStar_Syntax_Syntax.n
         in
      match uu____16833 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16839 -> false
  
let (is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  -> is_fvar FStar_Parser_Const.synth_lid t 
let (has_attribute :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Ident.lident -> Prims.bool)
  = fun attrs  -> fun attr  -> FStar_Util.for_some (is_fvar attr) attrs 
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options1 t s =
        let uu____16888 = FStar_Options.set_options t s  in
        match uu____16888 with
        | FStar_Getopt.Success  -> ()
        | FStar_Getopt.Help  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                "Failed to process pragma: use 'fstar --help' to see which options are available")
              r
        | FStar_Getopt.Error s1 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                (Prims.strcat "Failed to process pragma: " s1)) r
         in
      match p with
      | FStar_Syntax_Syntax.LightOff  ->
          if p = FStar_Syntax_Syntax.LightOff
          then FStar_Options.set_ml_ish ()
          else ()
      | FStar_Syntax_Syntax.SetOptions o -> set_options1 FStar_Options.Set o
      | FStar_Syntax_Syntax.ResetOptions sopt ->
          ((let uu____16905 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16905 (fun a1  -> ()));
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
      | FStar_Syntax_Syntax.PushOptions sopt ->
          (FStar_Options.internal_push ();
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
      | FStar_Syntax_Syntax.PopOptions  ->
          let uu____16920 = FStar_Options.internal_pop ()  in
          if uu____16920
          then ()
          else
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                "Cannot #pop-options, stack would become empty") r
  
let rec (unbound_variables :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun tm  ->
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16952 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____16979 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____16994 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____16995 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____16996 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17005) ->
        let uu____17030 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17030 with
         | (bs1,t2) ->
             let uu____17039 =
               FStar_List.collect
                 (fun uu____17051  ->
                    match uu____17051 with
                    | (b,uu____17061) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17066 = unbound_variables t2  in
             FStar_List.append uu____17039 uu____17066)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17091 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17091 with
         | (bs1,c1) ->
             let uu____17100 =
               FStar_List.collect
                 (fun uu____17112  ->
                    match uu____17112 with
                    | (b,uu____17122) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17127 = unbound_variables_comp c1  in
             FStar_List.append uu____17100 uu____17127)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17136 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17136 with
         | (bs,t2) ->
             let uu____17159 =
               FStar_List.collect
                 (fun uu____17171  ->
                    match uu____17171 with
                    | (b1,uu____17181) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17186 = unbound_variables t2  in
             FStar_List.append uu____17159 uu____17186)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17215 =
          FStar_List.collect
            (fun uu____17229  ->
               match uu____17229 with
               | (x,uu____17241) -> unbound_variables x) args
           in
        let uu____17250 = unbound_variables t1  in
        FStar_List.append uu____17215 uu____17250
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17291 = unbound_variables t1  in
        let uu____17294 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17309 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17309 with
                  | (p,wopt,t2) ->
                      let uu____17331 = unbound_variables t2  in
                      let uu____17334 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17331 uu____17334))
           in
        FStar_List.append uu____17291 uu____17294
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17348) ->
        let uu____17389 = unbound_variables t1  in
        let uu____17392 =
          let uu____17395 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17426 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17395 uu____17426  in
        FStar_List.append uu____17389 uu____17392
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17467 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17470 =
          let uu____17473 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17476 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17481 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17483 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17483 with
                 | (uu____17504,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17473 uu____17476  in
        FStar_List.append uu____17467 uu____17470
    | FStar_Syntax_Syntax.Tm_let ((uu____17506,lbs),t1) ->
        let uu____17526 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17526 with
         | (lbs1,t2) ->
             let uu____17541 = unbound_variables t2  in
             let uu____17544 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17551 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17554 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17551 uu____17554) lbs1
                in
             FStar_List.append uu____17541 uu____17544)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17571 = unbound_variables t1  in
        let uu____17574 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17613  ->
                      match uu____17613 with
                      | (a,uu____17625) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17634,uu____17635,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17641,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17647 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17656 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17657 -> []  in
        FStar_List.append uu____17571 uu____17574

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17664) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17674) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17684 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17687 =
          FStar_List.collect
            (fun uu____17701  ->
               match uu____17701 with
               | (a,uu____17713) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17684 uu____17687

let (extract_attr' :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.term Prims.list ->
      (FStar_Syntax_Syntax.term Prims.list,FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun attr_lid  ->
    fun attrs  ->
      let rec aux acc attrs1 =
        match attrs1 with
        | [] -> FStar_Pervasives_Native.None
        | h::t ->
            let uu____17828 = head_and_args h  in
            (match uu____17828 with
             | (head1,args) ->
                 let uu____17889 =
                   let uu____17890 = FStar_Syntax_Subst.compress head1  in
                   uu____17890.FStar_Syntax_Syntax.n  in
                 (match uu____17889 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____17943 -> aux (h :: acc) t))
         in
      aux [] attrs
  
let (extract_attr :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun attr_lid  ->
    fun se  ->
      let uu____17967 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____17967 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___133_18009 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___133_18009.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___133_18009.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___133_18009.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___133_18009.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  