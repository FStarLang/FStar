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
    let t1 = unmeta_safe t  in
    let uu____2023 =
      let uu____2024 = FStar_Syntax_Subst.compress t1  in
      uu____2024.FStar_Syntax_Syntax.n  in
    match uu____2023 with
    | FStar_Syntax_Syntax.Tm_app (t2,uu____2028) -> head_of t2
    | FStar_Syntax_Syntax.Tm_match (t2,uu____2054) -> head_of t2
    | FStar_Syntax_Syntax.Tm_abs (uu____2091,t2,uu____2093) -> head_of t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2119,uu____2120) ->
        head_of t2
    | uu____2161 -> t1
  
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
    | uu____2239 -> (t1, [])
  
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
        let uu____2321 = head_and_args' head1  in
        (match uu____2321 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____2390 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2417) ->
        FStar_Syntax_Subst.compress t2
    | uu____2422 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2430 =
      let uu____2431 = FStar_Syntax_Subst.compress t  in
      uu____2431.FStar_Syntax_Syntax.n  in
    match uu____2430 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____2435,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____2463)::uu____2464 ->
                  let pats' = unmeta pats  in
                  let uu____2524 = head_and_args pats'  in
                  (match uu____2524 with
                   | (head1,uu____2543) ->
                       let uu____2568 =
                         let uu____2569 = un_uinst head1  in
                         uu____2569.FStar_Syntax_Syntax.n  in
                       (match uu____2568 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____2574 -> false))
              | uu____2576 -> false)
         | uu____2588 -> false)
    | uu____2590 -> false
  
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
                (fun uu___119_2609  ->
                   match uu___119_2609 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2612 -> false)))
    | uu____2614 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2631) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2641) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2670 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2679 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___129_2691 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___129_2691.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___129_2691.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___129_2691.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___129_2691.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2705  ->
           let uu____2706 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____2706 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___120_2724  ->
            match uu___120_2724 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2728 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2736 -> []
    | FStar_Syntax_Syntax.GTotal uu____2753 -> []
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
    | uu____2797 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2807,uu____2808) ->
        unascribe e2
    | uu____2849 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2902,uu____2903) ->
          ascribe t' k
      | uu____2944 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2971 =
      let uu____2980 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2980  in
    uu____2971 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3036 =
      let uu____3037 = FStar_Syntax_Subst.compress t  in
      uu____3037.FStar_Syntax_Syntax.n  in
    match uu____3036 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____3041 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____3041
    | uu____3042 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3049 =
      let uu____3050 = FStar_Syntax_Subst.compress t  in
      uu____3050.FStar_Syntax_Syntax.n  in
    match uu____3049 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____3054 ->
             let uu____3063 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____3063
         | uu____3064 -> t)
    | uu____3065 -> t
  
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
      | uu____3089 -> false
  
let rec unlazy_as_t :
  'Auu____3102 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____3102
  =
  fun k  ->
    fun t  ->
      let uu____3113 =
        let uu____3114 = FStar_Syntax_Subst.compress t  in
        uu____3114.FStar_Syntax_Syntax.n  in
      match uu____3113 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____3119;
            FStar_Syntax_Syntax.rng = uu____3120;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____3123 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____3164 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____3164;
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
    let uu____3177 =
      let uu____3192 = unascribe t  in head_and_args' uu____3192  in
    match uu____3177 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____3226 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____3237 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____3248 -> false
  
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
      | (NotEqual ,uu____3298) -> NotEqual
      | (uu____3299,NotEqual ) -> NotEqual
      | (Unknown ,uu____3300) -> Unknown
      | (uu____3301,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___121_3422 = if uu___121_3422 then Equal else Unknown
         in
      let equal_iff uu___122_3433 = if uu___122_3433 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____3454 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3476 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3476
        then
          let uu____3480 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3557  ->
                    match uu____3557 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3598 = eq_tm a1 a2  in
                        eq_inj acc uu____3598) Equal) uu____3480
        else NotEqual  in
      let uu____3601 =
        let uu____3606 =
          let uu____3607 = unmeta t11  in uu____3607.FStar_Syntax_Syntax.n
           in
        let uu____3610 =
          let uu____3611 = unmeta t21  in uu____3611.FStar_Syntax_Syntax.n
           in
        (uu____3606, uu____3610)  in
      match uu____3601 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3617,uu____3618) ->
          let uu____3619 = unlazy t11  in eq_tm uu____3619 t21
      | (uu____3620,FStar_Syntax_Syntax.Tm_lazy uu____3621) ->
          let uu____3622 = unlazy t21  in eq_tm t11 uu____3622
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
            (let uu____3650 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____3650)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3664 = eq_tm f g  in
          eq_and uu____3664
            (fun uu____3667  ->
               let uu____3668 = eq_univs_list us vs  in equal_if uu____3668)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3670),uu____3671) -> Unknown
      | (uu____3672,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3673)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3676 = FStar_Const.eq_const c d  in equal_iff uu____3676
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3679)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3681))) ->
          let uu____3710 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3710
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3764 =
            let uu____3769 =
              let uu____3770 = un_uinst h1  in
              uu____3770.FStar_Syntax_Syntax.n  in
            let uu____3773 =
              let uu____3774 = un_uinst h2  in
              uu____3774.FStar_Syntax_Syntax.n  in
            (uu____3769, uu____3773)  in
          (match uu____3764 with
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
                 (let uu____3786 =
                    let uu____3788 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3788  in
                  FStar_List.mem uu____3786 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3790 ->
               let uu____3795 = eq_tm h1 h2  in
               eq_and uu____3795 (fun uu____3797  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3903 = FStar_List.zip bs1 bs2  in
            let uu____3966 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____4003  ->
                 fun a  ->
                   match uu____4003 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4096  -> branch_matches b1 b2))
              uu____3903 uu____3966
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____4101 = eq_univs u v1  in equal_if uu____4101
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____4115 = eq_quoteinfo q1 q2  in
          eq_and uu____4115 (fun uu____4117  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____4130 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4130 (fun uu____4132  -> eq_tm phi1 phi2)
      | uu____4133 -> Unknown

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
      | ([],uu____4205) -> NotEqual
      | (uu____4236,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____4328 = eq_tm t1 t2  in
             match uu____4328 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4329 = eq_antiquotes a11 a21  in
                 (match uu____4329 with
                  | NotEqual  -> NotEqual
                  | uu____4330 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____4345) -> NotEqual
      | (uu____4352,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4382 -> NotEqual

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
        | (uu____4474,uu____4475) -> false  in
      let uu____4485 = b1  in
      match uu____4485 with
      | (p1,w1,t1) ->
          let uu____4519 = b2  in
          (match uu____4519 with
           | (p2,w2,t2) ->
               let uu____4553 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4553
               then
                 let uu____4556 =
                   (let uu____4560 = eq_tm t1 t2  in uu____4560 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4569 = eq_tm t11 t21  in
                             uu____4569 = Equal) w1 w2)
                    in
                 (if uu____4556 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4634)::a11,(b,uu____4637)::b1) ->
          let uu____4711 = eq_tm a b  in
          (match uu____4711 with
           | Equal  -> eq_args a11 b1
           | uu____4712 -> Unknown)
      | uu____4713 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4749) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4755,uu____4756) ->
        unrefine t2
    | uu____4797 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4805 =
      let uu____4806 = FStar_Syntax_Subst.compress t  in
      uu____4806.FStar_Syntax_Syntax.n  in
    match uu____4805 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4810 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4825) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4830 ->
        let uu____4847 =
          let uu____4848 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4848 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4847 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4911,uu____4912) ->
        is_uvar t1
    | uu____4953 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4962 =
      let uu____4963 = unrefine t  in uu____4963.FStar_Syntax_Syntax.n  in
    match uu____4962 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4969) -> is_unit t1
    | uu____4974 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4983 =
      let uu____4984 = FStar_Syntax_Subst.compress t  in
      uu____4984.FStar_Syntax_Syntax.n  in
    match uu____4983 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____4989 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4998 =
      let uu____4999 = unrefine t  in uu____4999.FStar_Syntax_Syntax.n  in
    match uu____4998 with
    | FStar_Syntax_Syntax.Tm_type uu____5003 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____5007) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5033) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____5038,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____5060 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5069 =
      let uu____5070 = FStar_Syntax_Subst.compress e  in
      uu____5070.FStar_Syntax_Syntax.n  in
    match uu____5069 with
    | FStar_Syntax_Syntax.Tm_abs uu____5074 -> true
    | uu____5094 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5103 =
      let uu____5104 = FStar_Syntax_Subst.compress t  in
      uu____5104.FStar_Syntax_Syntax.n  in
    match uu____5103 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5108 -> true
    | uu____5124 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5134) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5140,uu____5141) ->
        pre_typ t2
    | uu____5182 -> t1
  
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
      let uu____5207 =
        let uu____5208 = un_uinst typ1  in uu____5208.FStar_Syntax_Syntax.n
         in
      match uu____5207 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5273 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5303 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5324,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5331) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5336,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5347,uu____5348,uu____5349,uu____5350,uu____5351) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5361,uu____5362,uu____5363,uu____5364) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5370,uu____5371,uu____5372,uu____5373,uu____5374) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5382,uu____5383) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5385,uu____5386) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5389 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5390 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5391 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5405 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___123_5431  ->
    match uu___123_5431 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5445 'Auu____5446 .
    ('Auu____5445 FStar_Syntax_Syntax.syntax,'Auu____5446)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____5457  ->
    match uu____5457 with | (hd1,uu____5465) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5479 'Auu____5480 .
    ('Auu____5479 FStar_Syntax_Syntax.syntax,'Auu____5480)
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
      | uu____5578 ->
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
      let uu____5637 =
        FStar_List.map
          (fun uu____5664  ->
             match uu____5664 with
             | (bv,aq) ->
                 let uu____5683 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5683, aq)) bs
         in
      mk_app f uu____5637
  
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
          let uu____5733 = FStar_Ident.range_of_lid l  in
          let uu____5734 =
            let uu____5743 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5743  in
          uu____5734 FStar_Pervasives_Native.None uu____5733
      | uu____5751 ->
          let e =
            let uu____5765 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5765 args  in
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
          let uu____5842 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5842
          then
            let uu____5845 =
              let uu____5851 =
                let uu____5853 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____5853  in
              let uu____5856 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5851, uu____5856)  in
            FStar_Ident.mk_ident uu____5845
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___130_5861 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___130_5861.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___130_5861.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5862 = mk_field_projector_name_from_ident lid nm  in
        (uu____5862, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5874) -> ses
    | uu____5883 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____5894 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5907 = FStar_Syntax_Unionfind.find uv  in
      match uu____5907 with
      | FStar_Pervasives_Native.Some uu____5910 ->
          let uu____5911 =
            let uu____5913 =
              let uu____5915 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5915  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5913  in
          failwith uu____5911
      | uu____5920 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____6003 -> q1 = q2
  
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
              let uu____6049 =
                let uu___131_6050 = rc  in
                let uu____6051 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___131_6050.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6051;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___131_6050.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6049
           in
        match bs with
        | [] -> t
        | uu____6068 ->
            let body =
              let uu____6070 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6070  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6100 =
                   let uu____6107 =
                     let uu____6108 =
                       let uu____6127 =
                         let uu____6136 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6136 bs'  in
                       let uu____6151 = close_lopt lopt'  in
                       (uu____6127, t1, uu____6151)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6108  in
                   FStar_Syntax_Syntax.mk uu____6107  in
                 uu____6100 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6169 ->
                 let uu____6170 =
                   let uu____6177 =
                     let uu____6178 =
                       let uu____6197 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6206 = close_lopt lopt  in
                       (uu____6197, body, uu____6206)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6178  in
                   FStar_Syntax_Syntax.mk uu____6177  in
                 uu____6170 FStar_Pervasives_Native.None
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
      | uu____6265 ->
          let uu____6274 =
            let uu____6281 =
              let uu____6282 =
                let uu____6297 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6306 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6297, uu____6306)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6282  in
            FStar_Syntax_Syntax.mk uu____6281  in
          uu____6274 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
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
      let uu____6358 =
        let uu____6359 = FStar_Syntax_Subst.compress t  in
        uu____6359.FStar_Syntax_Syntax.n  in
      match uu____6358 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6389) ->
               let uu____6398 =
                 let uu____6399 = FStar_Syntax_Subst.compress tres  in
                 uu____6399.FStar_Syntax_Syntax.n  in
               (match uu____6398 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6442 -> t)
           | uu____6443 -> t)
      | uu____6444 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6462 =
        let uu____6463 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6463 t.FStar_Syntax_Syntax.pos  in
      let uu____6464 =
        let uu____6471 =
          let uu____6472 =
            let uu____6479 =
              let uu____6482 =
                let uu____6483 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6483]  in
              FStar_Syntax_Subst.close uu____6482 t  in
            (b, uu____6479)  in
          FStar_Syntax_Syntax.Tm_refine uu____6472  in
        FStar_Syntax_Syntax.mk uu____6471  in
      uu____6464 FStar_Pervasives_Native.None uu____6462
  
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
        let uu____6566 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6566 with
         | (bs1,c1) ->
             let uu____6585 = is_total_comp c1  in
             if uu____6585
             then
               let uu____6600 = arrow_formals_comp (comp_result c1)  in
               (match uu____6600 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6667;
           FStar_Syntax_Syntax.index = uu____6668;
           FStar_Syntax_Syntax.sort = s;_},uu____6670)
        ->
        let rec aux s1 k2 =
          let uu____6701 =
            let uu____6702 = FStar_Syntax_Subst.compress s1  in
            uu____6702.FStar_Syntax_Syntax.n  in
          match uu____6701 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6717 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6732;
                 FStar_Syntax_Syntax.index = uu____6733;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6735)
              -> aux s2 k2
          | uu____6743 ->
              let uu____6744 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6744)
           in
        aux s k1
    | uu____6759 ->
        let uu____6760 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6760)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                               FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____6795 = arrow_formals_comp k  in
    match uu____6795 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____6937 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6937 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6961 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___124_6970  ->
                         match uu___124_6970 with
                         | FStar_Syntax_Syntax.DECREASES uu____6972 -> true
                         | uu____6976 -> false))
                  in
               (match uu____6961 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7011 ->
                    let uu____7014 = is_total_comp c1  in
                    if uu____7014
                    then
                      let uu____7033 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7033 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7126;
             FStar_Syntax_Syntax.index = uu____7127;
             FStar_Syntax_Syntax.sort = k2;_},uu____7129)
          -> arrow_until_decreases k2
      | uu____7137 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7158 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7158 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7212 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7233 =
                 FStar_Common.tabulate n_univs (fun uu____7243  -> false)  in
               let uu____7246 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7271  ->
                         match uu____7271 with
                         | (x,uu____7280) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7233 uu____7246)
           in
        ((n_univs + (FStar_List.length bs)), uu____7212)
  
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
          let uu____7342 =
            let uu___132_7343 = rc  in
            let uu____7344 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___132_7343.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7344;
              FStar_Syntax_Syntax.residual_flags =
                (uu___132_7343.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7342
      | uu____7353 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7387 =
        let uu____7388 =
          let uu____7391 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7391  in
        uu____7388.FStar_Syntax_Syntax.n  in
      match uu____7387 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7437 = aux t2 what  in
          (match uu____7437 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7509 -> ([], t1, abs_body_lcomp)  in
    let uu____7526 = aux t FStar_Pervasives_Native.None  in
    match uu____7526 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7574 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7574 with
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
                    | (FStar_Pervasives_Native.None ,uu____7737) -> def
                    | (uu____7748,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7760) ->
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
            let uu____7857 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7857 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7892 ->
            let t' = arrow binders c  in
            let uu____7904 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____7904 with
             | (uvs1,t'1) ->
                 let uu____7925 =
                   let uu____7926 = FStar_Syntax_Subst.compress t'1  in
                   uu____7926.FStar_Syntax_Syntax.n  in
                 (match uu____7925 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____7975 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____8000 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8011 -> false
  
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
      let uu____8074 =
        let uu____8075 = pre_typ t  in uu____8075.FStar_Syntax_Syntax.n  in
      match uu____8074 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8080 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8094 =
        let uu____8095 = pre_typ t  in uu____8095.FStar_Syntax_Syntax.n  in
      match uu____8094 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8099 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8101) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8127) ->
          is_constructed_typ t1 lid
      | uu____8132 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8145 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8146 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8147 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8149) -> get_tycon t2
    | uu____8174 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8182 =
      let uu____8183 = un_uinst t  in uu____8183.FStar_Syntax_Syntax.n  in
    match uu____8182 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8188 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____8202 =
        let uu____8206 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____8206  in
      match uu____8202 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8238 -> false
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
  fun uu____8257  ->
    let u =
      let uu____8263 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_2  -> FStar_Syntax_Syntax.U_unif _0_2)
        uu____8263
       in
    let uu____8280 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8280, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8293 = eq_tm a a'  in
      match uu____8293 with | Equal  -> true | uu____8296 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8301 =
    let uu____8308 =
      let uu____8309 =
        let uu____8310 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8310
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8309  in
    FStar_Syntax_Syntax.mk uu____8308  in
  uu____8301 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8425 =
            let uu____8428 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8429 =
              let uu____8436 =
                let uu____8437 =
                  let uu____8454 =
                    let uu____8465 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8474 =
                      let uu____8485 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8485]  in
                    uu____8465 :: uu____8474  in
                  (tand, uu____8454)  in
                FStar_Syntax_Syntax.Tm_app uu____8437  in
              FStar_Syntax_Syntax.mk uu____8436  in
            uu____8429 FStar_Pervasives_Native.None uu____8428  in
          FStar_Pervasives_Native.Some uu____8425
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8565 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8566 =
          let uu____8573 =
            let uu____8574 =
              let uu____8591 =
                let uu____8602 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8611 =
                  let uu____8622 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8622]  in
                uu____8602 :: uu____8611  in
              (op_t, uu____8591)  in
            FStar_Syntax_Syntax.Tm_app uu____8574  in
          FStar_Syntax_Syntax.mk uu____8573  in
        uu____8566 FStar_Pervasives_Native.None uu____8565
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8682 =
      let uu____8689 =
        let uu____8690 =
          let uu____8707 =
            let uu____8718 = FStar_Syntax_Syntax.as_arg phi  in [uu____8718]
             in
          (t_not, uu____8707)  in
        FStar_Syntax_Syntax.Tm_app uu____8690  in
      FStar_Syntax_Syntax.mk uu____8689  in
    uu____8682 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____8918 =
      let uu____8925 =
        let uu____8926 =
          let uu____8943 =
            let uu____8954 = FStar_Syntax_Syntax.as_arg e  in [uu____8954]
             in
          (b2t_v, uu____8943)  in
        FStar_Syntax_Syntax.Tm_app uu____8926  in
      FStar_Syntax_Syntax.mk uu____8925  in
    uu____8918 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9001 =
      let uu____9002 = unmeta t  in uu____9002.FStar_Syntax_Syntax.n  in
    match uu____9001 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9007 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9030 = is_t_true t1  in
      if uu____9030
      then t2
      else
        (let uu____9037 = is_t_true t2  in
         if uu____9037 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9065 = is_t_true t1  in
      if uu____9065
      then t_true
      else
        (let uu____9072 = is_t_true t2  in
         if uu____9072 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9101 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9102 =
        let uu____9109 =
          let uu____9110 =
            let uu____9127 =
              let uu____9138 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9147 =
                let uu____9158 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9158]  in
              uu____9138 :: uu____9147  in
            (teq, uu____9127)  in
          FStar_Syntax_Syntax.Tm_app uu____9110  in
        FStar_Syntax_Syntax.mk uu____9109  in
      uu____9102 FStar_Pervasives_Native.None uu____9101
  
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
          let uu____9228 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9229 =
            let uu____9236 =
              let uu____9237 =
                let uu____9254 =
                  let uu____9265 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9274 =
                    let uu____9285 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9294 =
                      let uu____9305 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9305]  in
                    uu____9285 :: uu____9294  in
                  uu____9265 :: uu____9274  in
                (eq_inst, uu____9254)  in
              FStar_Syntax_Syntax.Tm_app uu____9237  in
            FStar_Syntax_Syntax.mk uu____9236  in
          uu____9229 FStar_Pervasives_Native.None uu____9228
  
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
        let uu____9385 =
          let uu____9392 =
            let uu____9393 =
              let uu____9410 =
                let uu____9421 = FStar_Syntax_Syntax.iarg t  in
                let uu____9430 =
                  let uu____9441 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9450 =
                    let uu____9461 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9461]  in
                  uu____9441 :: uu____9450  in
                uu____9421 :: uu____9430  in
              (t_has_type1, uu____9410)  in
            FStar_Syntax_Syntax.Tm_app uu____9393  in
          FStar_Syntax_Syntax.mk uu____9392  in
        uu____9385 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9541 =
          let uu____9548 =
            let uu____9549 =
              let uu____9566 =
                let uu____9577 = FStar_Syntax_Syntax.iarg t  in
                let uu____9586 =
                  let uu____9597 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9597]  in
                uu____9577 :: uu____9586  in
              (t_with_type1, uu____9566)  in
            FStar_Syntax_Syntax.Tm_app uu____9549  in
          FStar_Syntax_Syntax.mk uu____9548  in
        uu____9541 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9647 =
    let uu____9654 =
      let uu____9655 =
        let uu____9662 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9662, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9655  in
    FStar_Syntax_Syntax.mk uu____9654  in
  uu____9647 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____9680 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____9693 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____9704 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____9680 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____9725  -> c0)
  
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
        let uu____9808 =
          let uu____9815 =
            let uu____9816 =
              let uu____9833 =
                let uu____9844 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____9853 =
                  let uu____9864 =
                    let uu____9873 =
                      let uu____9874 =
                        let uu____9875 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____9875]  in
                      abs uu____9874 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____9873  in
                  [uu____9864]  in
                uu____9844 :: uu____9853  in
              (fa, uu____9833)  in
            FStar_Syntax_Syntax.Tm_app uu____9816  in
          FStar_Syntax_Syntax.mk uu____9815  in
        uu____9808 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10005 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10005
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10024 -> true
    | uu____10026 -> false
  
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
          let uu____10073 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10073, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10102 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10102, FStar_Pervasives_Native.None, t2)  in
        let uu____10116 =
          let uu____10117 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10117  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10116
  
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
      let uu____10193 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10196 =
        let uu____10207 = FStar_Syntax_Syntax.as_arg p  in [uu____10207]  in
      mk_app uu____10193 uu____10196
  
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
      let uu____10247 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10250 =
        let uu____10261 = FStar_Syntax_Syntax.as_arg p  in [uu____10261]  in
      mk_app uu____10247 uu____10250
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10296 = head_and_args t  in
    match uu____10296 with
    | (head1,args) ->
        let uu____10343 =
          let uu____10358 =
            let uu____10359 = un_uinst head1  in
            uu____10359.FStar_Syntax_Syntax.n  in
          (uu____10358, args)  in
        (match uu____10343 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10378)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10444 =
                    let uu____10449 =
                      let uu____10450 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10450]  in
                    FStar_Syntax_Subst.open_term uu____10449 p  in
                  (match uu____10444 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10507 -> failwith "impossible"  in
                       let uu____10515 =
                         let uu____10517 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10517
                          in
                       if uu____10515
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10533 -> FStar_Pervasives_Native.None)
         | uu____10536 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10567 = head_and_args t  in
    match uu____10567 with
    | (head1,args) ->
        let uu____10618 =
          let uu____10633 =
            let uu____10634 = FStar_Syntax_Subst.compress head1  in
            uu____10634.FStar_Syntax_Syntax.n  in
          (uu____10633, args)  in
        (match uu____10618 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10656;
               FStar_Syntax_Syntax.vars = uu____10657;_},u::[]),(t1,uu____10660)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10707 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10742 = head_and_args t  in
    match uu____10742 with
    | (head1,args) ->
        let uu____10793 =
          let uu____10808 =
            let uu____10809 = FStar_Syntax_Subst.compress head1  in
            uu____10809.FStar_Syntax_Syntax.n  in
          (uu____10808, args)  in
        (match uu____10793 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10831;
               FStar_Syntax_Syntax.vars = uu____10832;_},u::[]),(t1,uu____10835)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10882 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____10910 =
      let uu____10927 = unmeta t  in head_and_args uu____10927  in
    match uu____10910 with
    | (head1,uu____10930) ->
        let uu____10955 =
          let uu____10956 = un_uinst head1  in
          uu____10956.FStar_Syntax_Syntax.n  in
        (match uu____10955 with
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
         | uu____10961 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10981 =
      let uu____10994 =
        let uu____10995 = FStar_Syntax_Subst.compress t  in
        uu____10995.FStar_Syntax_Syntax.n  in
      match uu____10994 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____11125 =
            let uu____11136 =
              let uu____11137 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____11137  in
            (b, uu____11136)  in
          FStar_Pervasives_Native.Some uu____11125
      | uu____11154 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____10981
      (fun uu____11192  ->
         match uu____11192 with
         | (b,c) ->
             let uu____11229 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11229 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11292 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11329 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11329
  
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
    match projectee with | QAll _0 -> true | uu____11381 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11425 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11467 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11507) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11519) ->
          unmeta_monadic t
      | uu____11532 -> f2  in
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
      let aux f2 uu____11628 =
        match uu____11628 with
        | (lid,arity) ->
            let uu____11637 =
              let uu____11654 = unmeta_monadic f2  in
              head_and_args uu____11654  in
            (match uu____11637 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____11684 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____11684
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____11764 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____11764)
      | uu____11777 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____11844 = head_and_args t1  in
        match uu____11844 with
        | (t2,args) ->
            let uu____11899 = un_uinst t2  in
            let uu____11900 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____11941  ->
                      match uu____11941 with
                      | (t3,imp) ->
                          let uu____11960 = unascribe t3  in
                          (uu____11960, imp)))
               in
            (uu____11899, uu____11900)
         in
      let rec aux qopt out t1 =
        let uu____12011 = let uu____12035 = flat t1  in (qopt, uu____12035)
           in
        match uu____12011 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12075;
                 FStar_Syntax_Syntax.vars = uu____12076;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12079);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12080;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12081;_},uu____12082)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12184;
                 FStar_Syntax_Syntax.vars = uu____12185;_},uu____12186::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12189);
                  FStar_Syntax_Syntax.pos = uu____12190;
                  FStar_Syntax_Syntax.vars = uu____12191;_},uu____12192)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12309;
               FStar_Syntax_Syntax.vars = uu____12310;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12313);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12314;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12315;_},uu____12316)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12409 =
              let uu____12413 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12413  in
            aux uu____12409 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12423;
               FStar_Syntax_Syntax.vars = uu____12424;_},uu____12425::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12428);
                FStar_Syntax_Syntax.pos = uu____12429;
                FStar_Syntax_Syntax.vars = uu____12430;_},uu____12431)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12540 =
              let uu____12544 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12544  in
            aux uu____12540 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____12554) ->
            let bs = FStar_List.rev out  in
            let uu____12607 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____12607 with
             | (bs1,t2) ->
                 let uu____12616 = patterns t2  in
                 (match uu____12616 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____12666 -> FStar_Pervasives_Native.None  in
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
      let uu____12758 = un_squash t  in
      FStar_Util.bind_opt uu____12758
        (fun t1  ->
           let uu____12774 = head_and_args' t1  in
           match uu____12774 with
           | (hd1,args) ->
               let uu____12813 =
                 let uu____12819 =
                   let uu____12820 = un_uinst hd1  in
                   uu____12820.FStar_Syntax_Syntax.n  in
                 (uu____12819, (FStar_List.length args))  in
               (match uu____12813 with
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
                | uu____12850 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____12880 = un_squash t  in
      FStar_Util.bind_opt uu____12880
        (fun t1  ->
           let uu____12895 = arrow_one t1  in
           match uu____12895 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____12910 =
                 let uu____12912 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____12912  in
               if uu____12910
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____12922 = comp_to_comp_typ_nouniv c  in
                    uu____12922.FStar_Syntax_Syntax.result_typ  in
                  let uu____12923 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____12923
                  then
                    let uu____12930 = patterns q  in
                    match uu____12930 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____12993 =
                       let uu____12994 =
                         let uu____12999 =
                           let uu____13000 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13011 =
                             let uu____13022 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13022]  in
                           uu____13000 :: uu____13011  in
                         (FStar_Parser_Const.imp_lid, uu____12999)  in
                       BaseConn uu____12994  in
                     FStar_Pervasives_Native.Some uu____12993))
           | uu____13055 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13063 = un_squash t  in
      FStar_Util.bind_opt uu____13063
        (fun t1  ->
           let uu____13094 = head_and_args' t1  in
           match uu____13094 with
           | (hd1,args) ->
               let uu____13133 =
                 let uu____13148 =
                   let uu____13149 = un_uinst hd1  in
                   uu____13149.FStar_Syntax_Syntax.n  in
                 (uu____13148, args)  in
               (match uu____13133 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13166)::(a2,uu____13168)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13219 =
                      let uu____13220 = FStar_Syntax_Subst.compress a2  in
                      uu____13220.FStar_Syntax_Syntax.n  in
                    (match uu____13219 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13227) ->
                         let uu____13262 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13262 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13315 -> failwith "impossible"  in
                              let uu____13323 = patterns q1  in
                              (match uu____13323 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13384 -> FStar_Pervasives_Native.None)
                | uu____13385 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13408 = destruct_sq_forall phi  in
          (match uu____13408 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_11  -> FStar_Pervasives_Native.Some _0_11)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13424 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13430 = destruct_sq_exists phi  in
          (match uu____13430 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_12  -> FStar_Pervasives_Native.Some _0_12)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13446 -> f1)
      | uu____13449 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13453 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13453
      (fun uu____13458  ->
         let uu____13459 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13459
           (fun uu____13464  ->
              let uu____13465 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13465
                (fun uu____13470  ->
                   let uu____13471 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13471
                     (fun uu____13476  ->
                        let uu____13477 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13477
                          (fun uu____13481  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____13494 =
      let uu____13495 = FStar_Syntax_Subst.compress t  in
      uu____13495.FStar_Syntax_Syntax.n  in
    match uu____13494 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____13502) ->
        let uu____13537 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____13537 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____13571 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____13571
             then
               let uu____13578 =
                 let uu____13589 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____13589]  in
               mk_app t uu____13578
             else e1)
    | uu____13616 ->
        let uu____13617 =
          let uu____13628 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____13628]  in
        mk_app t uu____13617
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13670 =
            let uu____13675 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13675  in
          let uu____13676 =
            let uu____13677 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13677  in
          let uu____13680 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13670 a.FStar_Syntax_Syntax.action_univs uu____13676
            FStar_Parser_Const.effect_Tot_lid uu____13680 [] pos
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
    let uu____13706 =
      let uu____13713 =
        let uu____13714 =
          let uu____13731 =
            let uu____13742 = FStar_Syntax_Syntax.as_arg t  in [uu____13742]
             in
          (reify_1, uu____13731)  in
        FStar_Syntax_Syntax.Tm_app uu____13714  in
      FStar_Syntax_Syntax.mk uu____13713  in
    uu____13706 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____13797 =
        let uu____13804 =
          let uu____13805 =
            let uu____13806 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____13806  in
          FStar_Syntax_Syntax.Tm_constant uu____13805  in
        FStar_Syntax_Syntax.mk uu____13804  in
      uu____13797 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____13811 =
      let uu____13818 =
        let uu____13819 =
          let uu____13836 =
            let uu____13847 = FStar_Syntax_Syntax.as_arg t  in [uu____13847]
             in
          (reflect_, uu____13836)  in
        FStar_Syntax_Syntax.Tm_app uu____13819  in
      FStar_Syntax_Syntax.mk uu____13818  in
    uu____13811 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13894 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____13919 = unfold_lazy i  in delta_qualifier uu____13919
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____13921 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____13922 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____13923 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____13946 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____13959 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____13960 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____13967 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____13968 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____13984) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____13989;
           FStar_Syntax_Syntax.index = uu____13990;
           FStar_Syntax_Syntax.sort = t2;_},uu____13992)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14001) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14007,uu____14008) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14050) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14075,t2,uu____14077) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14102,t2) -> delta_qualifier t2
  
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
    let uu____14141 = delta_qualifier t  in incr_delta_depth uu____14141
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14149 =
      let uu____14150 = FStar_Syntax_Subst.compress t  in
      uu____14150.FStar_Syntax_Syntax.n  in
    match uu____14149 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14155 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____14171 =
      let uu____14188 = unmeta e  in head_and_args uu____14188  in
    match uu____14171 with
    | (head1,args) ->
        let uu____14219 =
          let uu____14234 =
            let uu____14235 = un_uinst head1  in
            uu____14235.FStar_Syntax_Syntax.n  in
          (uu____14234, args)  in
        (match uu____14219 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____14253) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____14277::(hd1,uu____14279)::(tl1,uu____14281)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____14348 =
               let uu____14351 =
                 let uu____14354 = list_elements tl1  in
                 FStar_Util.must uu____14354  in
               hd1 :: uu____14351  in
             FStar_Pervasives_Native.Some uu____14348
         | uu____14363 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____14387 .
    ('Auu____14387 -> 'Auu____14387) ->
      'Auu____14387 Prims.list -> 'Auu____14387 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14413 = f a  in [uu____14413]
      | x::xs -> let uu____14418 = apply_last f xs  in x :: uu____14418
  
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
          let uu____14473 =
            let uu____14480 =
              let uu____14481 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14481  in
            FStar_Syntax_Syntax.mk uu____14480  in
          uu____14473 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____14498 =
            let uu____14503 =
              let uu____14504 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14504
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14503 args  in
          uu____14498 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14520 =
            let uu____14525 =
              let uu____14526 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14526
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14525 args  in
          uu____14520 FStar_Pervasives_Native.None pos  in
        let uu____14529 =
          let uu____14530 =
            let uu____14531 = FStar_Syntax_Syntax.iarg typ  in [uu____14531]
             in
          nil uu____14530 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14565 =
                 let uu____14566 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14575 =
                   let uu____14586 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14595 =
                     let uu____14606 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14606]  in
                   uu____14586 :: uu____14595  in
                 uu____14566 :: uu____14575  in
               cons1 uu____14565 t.FStar_Syntax_Syntax.pos) l uu____14529
  
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
        | uu____14715 -> false
  
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
          | uu____14829 -> false
  
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
        | uu____14995 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15044 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15044
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
        let t11 = let uu____15266 = unmeta_safe t1  in canon_app uu____15266
           in
        let t21 = let uu____15272 = unmeta_safe t2  in canon_app uu____15272
           in
        let uu____15275 =
          let uu____15280 =
            let uu____15281 =
              let uu____15284 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15284  in
            uu____15281.FStar_Syntax_Syntax.n  in
          let uu____15285 =
            let uu____15286 =
              let uu____15289 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15289  in
            uu____15286.FStar_Syntax_Syntax.n  in
          (uu____15280, uu____15285)  in
        match uu____15275 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15291,uu____15292) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15301,FStar_Syntax_Syntax.Tm_uinst uu____15302) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15311,uu____15312) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15337,FStar_Syntax_Syntax.Tm_delayed uu____15338) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15363,uu____15364) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15393,FStar_Syntax_Syntax.Tm_ascribed uu____15394) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15433 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15433
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15438 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15438
        | (FStar_Syntax_Syntax.Tm_type
           uu____15441,FStar_Syntax_Syntax.Tm_type uu____15442) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15500 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15500) &&
              (let uu____15510 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15510)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15559 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15559) &&
              (let uu____15569 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15569)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____15587 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15587)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15644 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15644) &&
              (let uu____15648 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15648)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15737 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15737) &&
              (let uu____15741 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15741)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15758,uu____15759) ->
            let uu____15760 =
              let uu____15762 = unlazy t11  in
              term_eq_dbg dbg uu____15762 t21  in
            check "lazy_l" uu____15760
        | (uu____15764,FStar_Syntax_Syntax.Tm_lazy uu____15765) ->
            let uu____15766 =
              let uu____15768 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15768  in
            check "lazy_r" uu____15766
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15813 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15813))
              &&
              (let uu____15817 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15817)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15821),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15823)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15881 =
               let uu____15883 = eq_quoteinfo qi1 qi2  in uu____15883 = Equal
                in
             check "tm_quoted qi" uu____15881) &&
              (let uu____15886 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15886)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15916 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15916) &&
                   (let uu____15920 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15920)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15939 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15939) &&
                    (let uu____15943 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15943))
                   &&
                   (let uu____15947 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15947)
             | uu____15950 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15956) -> fail "unk"
        | (uu____15958,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15960,uu____15961) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15963,uu____15964) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15966,uu____15967) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15969,uu____15970) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15972,uu____15973) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15975,uu____15976) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15996,uu____15997) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____16013,uu____16014) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____16022,uu____16023) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____16041,uu____16042) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16066,uu____16067) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16082,uu____16083) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16097,uu____16098) ->
            fail "bottom"
        | (uu____16106,FStar_Syntax_Syntax.Tm_bvar uu____16107) ->
            fail "bottom"
        | (uu____16109,FStar_Syntax_Syntax.Tm_name uu____16110) ->
            fail "bottom"
        | (uu____16112,FStar_Syntax_Syntax.Tm_fvar uu____16113) ->
            fail "bottom"
        | (uu____16115,FStar_Syntax_Syntax.Tm_constant uu____16116) ->
            fail "bottom"
        | (uu____16118,FStar_Syntax_Syntax.Tm_type uu____16119) ->
            fail "bottom"
        | (uu____16121,FStar_Syntax_Syntax.Tm_abs uu____16122) ->
            fail "bottom"
        | (uu____16142,FStar_Syntax_Syntax.Tm_arrow uu____16143) ->
            fail "bottom"
        | (uu____16159,FStar_Syntax_Syntax.Tm_refine uu____16160) ->
            fail "bottom"
        | (uu____16168,FStar_Syntax_Syntax.Tm_app uu____16169) ->
            fail "bottom"
        | (uu____16187,FStar_Syntax_Syntax.Tm_match uu____16188) ->
            fail "bottom"
        | (uu____16212,FStar_Syntax_Syntax.Tm_let uu____16213) ->
            fail "bottom"
        | (uu____16228,FStar_Syntax_Syntax.Tm_uvar uu____16229) ->
            fail "bottom"
        | (uu____16243,FStar_Syntax_Syntax.Tm_meta uu____16244) ->
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
               let uu____16279 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16279)
          (fun q1  ->
             fun q2  ->
               let uu____16291 =
                 let uu____16293 = eq_aqual q1 q2  in uu____16293 = Equal  in
               check "arg qual" uu____16291) a1 a2

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
               let uu____16318 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16318)
          (fun q1  ->
             fun q2  ->
               let uu____16330 =
                 let uu____16332 = eq_aqual q1 q2  in uu____16332 = Equal  in
               check "binder qual" uu____16330) b1 b2

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
        ((let uu____16352 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16352) &&
           (let uu____16356 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16356))
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
    fun uu____16366  ->
      fun uu____16367  ->
        match (uu____16366, uu____16367) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16494 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16494) &&
               (let uu____16498 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16498))
              &&
              (let uu____16502 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16544 -> false  in
               check "branch when" uu____16502)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16565 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16565) &&
           (let uu____16574 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16574))
          &&
          (let uu____16578 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16578)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16595 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16595 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16649 ->
        let uu____16672 =
          let uu____16674 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16674  in
        (Prims.parse_int "1") + uu____16672
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16677 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____16677
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16681 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____16681
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16690 = sizeof t1  in (FStar_List.length us) + uu____16690
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16694) ->
        let uu____16719 = sizeof t1  in
        let uu____16721 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16736  ->
                 match uu____16736 with
                 | (bv,uu____16746) ->
                     let uu____16751 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16751) (Prims.parse_int "0") bs
           in
        uu____16719 + uu____16721
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____16780 = sizeof hd1  in
        let uu____16782 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16797  ->
                 match uu____16797 with
                 | (arg,uu____16807) ->
                     let uu____16812 = sizeof arg  in acc + uu____16812)
            (Prims.parse_int "0") args
           in
        uu____16780 + uu____16782
    | uu____16815 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16829 =
        let uu____16830 = un_uinst t  in uu____16830.FStar_Syntax_Syntax.n
         in
      match uu____16829 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16835 -> false
  
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
        let uu____16884 = FStar_Options.set_options t s  in
        match uu____16884 with
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
          ((let uu____16901 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16901 (fun a1  -> ()));
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
          let uu____16916 = FStar_Options.internal_pop ()  in
          if uu____16916
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
    | FStar_Syntax_Syntax.Tm_delayed uu____16948 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____16975 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____16990 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____16991 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____16992 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17001) ->
        let uu____17026 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17026 with
         | (bs1,t2) ->
             let uu____17035 =
               FStar_List.collect
                 (fun uu____17047  ->
                    match uu____17047 with
                    | (b,uu____17057) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17062 = unbound_variables t2  in
             FStar_List.append uu____17035 uu____17062)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17087 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17087 with
         | (bs1,c1) ->
             let uu____17096 =
               FStar_List.collect
                 (fun uu____17108  ->
                    match uu____17108 with
                    | (b,uu____17118) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17123 = unbound_variables_comp c1  in
             FStar_List.append uu____17096 uu____17123)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17132 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17132 with
         | (bs,t2) ->
             let uu____17155 =
               FStar_List.collect
                 (fun uu____17167  ->
                    match uu____17167 with
                    | (b1,uu____17177) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17182 = unbound_variables t2  in
             FStar_List.append uu____17155 uu____17182)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17211 =
          FStar_List.collect
            (fun uu____17225  ->
               match uu____17225 with
               | (x,uu____17237) -> unbound_variables x) args
           in
        let uu____17246 = unbound_variables t1  in
        FStar_List.append uu____17211 uu____17246
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17287 = unbound_variables t1  in
        let uu____17290 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17305 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17305 with
                  | (p,wopt,t2) ->
                      let uu____17327 = unbound_variables t2  in
                      let uu____17330 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17327 uu____17330))
           in
        FStar_List.append uu____17287 uu____17290
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17344) ->
        let uu____17385 = unbound_variables t1  in
        let uu____17388 =
          let uu____17391 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17422 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17391 uu____17422  in
        FStar_List.append uu____17385 uu____17388
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17463 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17466 =
          let uu____17469 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17472 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17477 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17479 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17479 with
                 | (uu____17500,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17469 uu____17472  in
        FStar_List.append uu____17463 uu____17466
    | FStar_Syntax_Syntax.Tm_let ((uu____17502,lbs),t1) ->
        let uu____17522 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17522 with
         | (lbs1,t2) ->
             let uu____17537 = unbound_variables t2  in
             let uu____17540 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17547 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17550 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17547 uu____17550) lbs1
                in
             FStar_List.append uu____17537 uu____17540)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17567 = unbound_variables t1  in
        let uu____17570 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17609  ->
                      match uu____17609 with
                      | (a,uu____17621) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17630,uu____17631,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17637,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17643 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17652 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17653 -> []  in
        FStar_List.append uu____17567 uu____17570

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17660) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17670) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17680 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17683 =
          FStar_List.collect
            (fun uu____17697  ->
               match uu____17697 with
               | (a,uu____17709) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17680 uu____17683

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
            let uu____17824 = head_and_args h  in
            (match uu____17824 with
             | (head1,args) ->
                 let uu____17885 =
                   let uu____17886 = FStar_Syntax_Subst.compress head1  in
                   uu____17886.FStar_Syntax_Syntax.n  in
                 (match uu____17885 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____17939 -> aux (h :: acc) t))
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
      let uu____17963 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____17963 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___133_18005 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___133_18005.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___133_18005.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___133_18005.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___133_18005.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  