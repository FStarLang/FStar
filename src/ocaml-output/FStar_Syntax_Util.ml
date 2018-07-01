open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____32 = FStar_ST.op_Bang tts_f  in
    match uu____32 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____87 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____87 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____93 =
      let uu____96 =
        let uu____99 =
          FStar_Ident.mk_ident
            ((Prims.strcat FStar_Ident.reserved_prefix
                (Prims.strcat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____99]  in
      FStar_List.append lid.FStar_Ident.ns uu____96  in
    FStar_Ident.lid_of_ids uu____93
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____111 .
    (FStar_Syntax_Syntax.bv,'Auu____111) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term,'Auu____111) FStar_Pervasives_Native.tuple2
  =
  fun uu____124  ->
    match uu____124 with
    | (b,imp) ->
        let uu____131 = FStar_Syntax_Syntax.bv_to_name b  in (uu____131, imp)
  
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
            let uu____182 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____182
            then []
            else (let uu____198 = arg_of_non_null_binder b  in [uu____198])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  =
  fun binders  ->
    let uu____232 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____314 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____314
              then
                let b1 =
                  let uu____338 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____338, (FStar_Pervasives_Native.snd b))  in
                let uu____345 = arg_of_non_null_binder b1  in (b1, uu____345)
              else
                (let uu____367 = arg_of_non_null_binder b  in (b, uu____367))))
       in
    FStar_All.pipe_right uu____232 FStar_List.unzip
  
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
              let uu____499 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____499
              then
                let uu____506 = b  in
                match uu____506 with
                | (a,imp) ->
                    let b1 =
                      let uu____526 =
                        let uu____527 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____527  in
                      FStar_Ident.id_of_text uu____526  in
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
        let uu____567 =
          let uu____574 =
            let uu____575 =
              let uu____590 = name_binders binders  in (uu____590, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____575  in
          FStar_Syntax_Syntax.mk uu____574  in
        uu____567 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____612 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____648  ->
            match uu____648 with
            | (t,imp) ->
                let uu____659 =
                  let uu____660 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____660
                   in
                (uu____659, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____714  ->
            match uu____714 with
            | (t,imp) ->
                let uu____731 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____731, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____743 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____743
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____754 . 'Auu____754 -> 'Auu____754 Prims.list =
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
          (fun uu____874  ->
             fun uu____875  ->
               match (uu____874, uu____875) with
               | ((x,uu____901),(y,uu____903)) ->
                   let uu____924 =
                     let uu____931 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____931)  in
                   FStar_Syntax_Syntax.NT uu____924) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____944) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____950,uu____951) -> unmeta e2
    | uu____992 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____1005 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____1012 -> e1
         | uu____1021 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1023,uu____1024) ->
        unmeta_safe e2
    | uu____1065 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____1079 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____1080 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1090 = univ_kernel u1  in
        (match uu____1090 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____1101 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____1108 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____1118 = univ_kernel u  in FStar_Pervasives_Native.snd uu____1118
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____1133,uu____1134) ->
          failwith "Impossible: compare_univs"
      | (uu____1135,FStar_Syntax_Syntax.U_bvar uu____1136) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____1137) ->
          ~- (Prims.parse_int "1")
      | (uu____1138,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____1139) -> ~- (Prims.parse_int "1")
      | (uu____1140,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____1143,FStar_Syntax_Syntax.U_unif
         uu____1144) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____1153,FStar_Syntax_Syntax.U_name
         uu____1154) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____1181 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____1182 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____1181 - uu____1182
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____1213 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____1213
                 (fun uu____1228  ->
                    match uu____1228 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1242,uu____1243) ->
          ~- (Prims.parse_int "1")
      | (uu____1246,FStar_Syntax_Syntax.U_max uu____1247) ->
          (Prims.parse_int "1")
      | uu____1250 ->
          let uu____1255 = univ_kernel u1  in
          (match uu____1255 with
           | (k1,n1) ->
               let uu____1262 = univ_kernel u2  in
               (match uu____1262 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1281 = compare_univs u1 u2  in
      uu____1281 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1296 =
        let uu____1297 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1297;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1296
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1316 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1325 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1347 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1356 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1382 =
          let uu____1383 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1383  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1382;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1412 =
          let uu____1413 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1413  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1412;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
  
let (comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    fun f  ->
      let uu___118_1448 = c  in
      let uu____1449 =
        let uu____1450 =
          let uu___119_1451 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___119_1451.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___119_1451.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___119_1451.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___119_1451.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1450  in
      {
        FStar_Syntax_Syntax.n = uu____1449;
        FStar_Syntax_Syntax.pos = (uu___118_1448.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___118_1448.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1476 -> c
        | FStar_Syntax_Syntax.GTotal uu____1485 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___120_1496 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___120_1496.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___120_1496.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___120_1496.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___120_1496.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___121_1497 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___121_1497.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___121_1497.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1500  ->
           let uu____1501 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1501)
  
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
    | uu____1540 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1551 -> true
    | FStar_Syntax_Syntax.GTotal uu____1560 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___106_1581  ->
               match uu___106_1581 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1582 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___107_1591  ->
               match uu___107_1591 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1592 -> false)))
  
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
            (fun uu___108_1601  ->
               match uu___108_1601 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1602 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___109_1615  ->
            match uu___109_1615 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1616 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___110_1625  ->
            match uu___110_1625 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1626 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1650 -> true
    | FStar_Syntax_Syntax.GTotal uu____1659 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___111_1672  ->
                   match uu___111_1672 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1673 -> false)))
  
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
            (fun uu___112_1706  ->
               match uu___112_1706 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1707 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1718 =
      let uu____1719 = FStar_Syntax_Subst.compress t  in
      uu____1719.FStar_Syntax_Syntax.n  in
    match uu____1718 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1722,c) -> is_pure_or_ghost_comp c
    | uu____1744 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1755 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1761 =
      let uu____1762 = FStar_Syntax_Subst.compress t  in
      uu____1762.FStar_Syntax_Syntax.n  in
    match uu____1761 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1765,c) -> is_lemma_comp c
    | uu____1787 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1793 =
      let uu____1794 = FStar_Syntax_Subst.compress t  in
      uu____1794.FStar_Syntax_Syntax.n  in
    match uu____1793 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1798) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____1824) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____1861,t1,uu____1863) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1889,uu____1890) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1932) -> head_of t1
    | uu____1937 -> t
  
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
    | uu____2014 -> (t1, [])
  
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
        let uu____2095 = head_and_args' head1  in
        (match uu____2095 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____2164 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2190) ->
        FStar_Syntax_Subst.compress t2
    | uu____2195 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2201 =
      let uu____2202 = FStar_Syntax_Subst.compress t  in
      uu____2202.FStar_Syntax_Syntax.n  in
    match uu____2201 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____2205,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____2231)::uu____2232 ->
                  let pats' = unmeta pats  in
                  let uu____2292 = head_and_args pats'  in
                  (match uu____2292 with
                   | (head1,uu____2310) ->
                       let uu____2335 =
                         let uu____2336 = un_uinst head1  in
                         uu____2336.FStar_Syntax_Syntax.n  in
                       (match uu____2335 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____2340 -> false))
              | uu____2341 -> false)
         | uu____2352 -> false)
    | uu____2353 -> false
  
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
                (fun uu___113_2367  ->
                   match uu___113_2367 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2368 -> false)))
    | uu____2369 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2384) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2394) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2422 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2431 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___122_2443 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___122_2443.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___122_2443.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___122_2443.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___122_2443.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2456  ->
           let uu____2457 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____2457 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___114_2472  ->
            match uu___114_2472 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2473 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2479 -> []
    | FStar_Syntax_Syntax.GTotal uu____2496 -> []
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
    | uu____2533 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2541,uu____2542) ->
        unascribe e2
    | uu____2583 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2635,uu____2636) ->
          ascribe t' k
      | uu____2677 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2703 =
      let uu____2712 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2712  in
    uu____2703 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2767 =
      let uu____2768 = FStar_Syntax_Subst.compress t  in
      uu____2768.FStar_Syntax_Syntax.n  in
    match uu____2767 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2772 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2772
    | uu____2773 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2779 =
      let uu____2780 = FStar_Syntax_Subst.compress t  in
      uu____2780.FStar_Syntax_Syntax.n  in
    match uu____2779 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2784 ->
             let uu____2793 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____2793
         | uu____2794 -> t)
    | uu____2795 -> t
  
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
      | (FStar_Syntax_Syntax.Lazy_sigelt ,FStar_Syntax_Syntax.Lazy_sigelt )
          -> true
      | (FStar_Syntax_Syntax.Lazy_uvar ,FStar_Syntax_Syntax.Lazy_uvar ) ->
          true
      | uu____2806 -> false
  
let rec unlazy_as_t :
  'Auu____2817 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2817
  =
  fun k  ->
    fun t  ->
      let uu____2828 =
        let uu____2829 = FStar_Syntax_Subst.compress t  in
        uu____2829.FStar_Syntax_Syntax.n  in
      match uu____2828 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2834;
            FStar_Syntax_Syntax.rng = uu____2835;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____2838 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2877 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2877;
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
    let uu____2889 =
      let uu____2904 = unascribe t  in head_and_args' uu____2904  in
    match uu____2889 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2934 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2940 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2946 -> false
  
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
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___115_3070 = if uu___115_3070 then Equal else Unknown
         in
      let equal_iff uu___116_3077 = if uu___116_3077 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____3095 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____3107) -> NotEqual
        | (uu____3108,NotEqual ) -> NotEqual
        | (Unknown ,uu____3109) -> Unknown
        | (uu____3110,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____3132 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3132
        then
          let uu____3134 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3211  ->
                    match uu____3211 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3252 = eq_tm a1 a2  in
                        eq_inj acc uu____3252) Equal) uu____3134
        else NotEqual  in
      let uu____3254 =
        let uu____3259 =
          let uu____3260 = unmeta t11  in uu____3260.FStar_Syntax_Syntax.n
           in
        let uu____3263 =
          let uu____3264 = unmeta t21  in uu____3264.FStar_Syntax_Syntax.n
           in
        (uu____3259, uu____3263)  in
      match uu____3254 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3269,uu____3270) ->
          let uu____3271 = unlazy t11  in eq_tm uu____3271 t21
      | (uu____3272,FStar_Syntax_Syntax.Tm_lazy uu____3273) ->
          let uu____3274 = unlazy t21  in eq_tm t11 uu____3274
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
            (let uu____3300 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____3300)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3313 = eq_tm f g  in
          eq_and uu____3313
            (fun uu____3316  ->
               let uu____3317 = eq_univs_list us vs  in equal_if uu____3317)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3318),uu____3319) -> Unknown
      | (uu____3320,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3321)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3324 = FStar_Const.eq_const c d  in equal_iff uu____3324
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3326)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3328))) ->
          let uu____3357 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3357
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3410 =
            let uu____3415 =
              let uu____3416 = un_uinst h1  in
              uu____3416.FStar_Syntax_Syntax.n  in
            let uu____3419 =
              let uu____3420 = un_uinst h2  in
              uu____3420.FStar_Syntax_Syntax.n  in
            (uu____3415, uu____3419)  in
          (match uu____3410 with
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
                 (let uu____3432 =
                    let uu____3433 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3433  in
                  FStar_List.mem uu____3432 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3434 ->
               let uu____3439 = eq_tm h1 h2  in
               eq_and uu____3439 (fun uu____3441  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3546 = FStar_List.zip bs1 bs2  in
            let uu____3609 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3646  ->
                 fun a  ->
                   match uu____3646 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3739  -> branch_matches b1 b2))
              uu____3546 uu____3609
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3743 = eq_univs u v1  in equal_if uu____3743
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____3756 = eq_quoteinfo q1 q2  in
          eq_and uu____3756 (fun uu____3758  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____3771 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____3771 (fun uu____3773  -> eq_tm phi1 phi2)
      | uu____3774 -> Unknown

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
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                         FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 Prims.list -> eq_result)
  =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ([],uu____3860) -> NotEqual
      | (uu____3899,[]) -> NotEqual
      | ((x1,b1,t1)::a11,(x2,b2,t2)::a21) ->
          if
            Prims.op_Negation
              ((FStar_Syntax_Syntax.bv_eq x1 x2) && (b1 = b2))
          then NotEqual
          else
            (let uu____4011 = eq_tm t1 t2  in
             match uu____4011 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4012 = eq_antiquotes a11 a21  in
                 (match uu____4012 with
                  | NotEqual  -> NotEqual
                  | uu____4013 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____4028) -> NotEqual
      | (uu____4035,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | uu____4058 -> NotEqual

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
        | (uu____4145,uu____4146) -> false  in
      let uu____4155 = b1  in
      match uu____4155 with
      | (p1,w1,t1) ->
          let uu____4189 = b2  in
          (match uu____4189 with
           | (p2,w2,t2) ->
               let uu____4223 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4223
               then
                 let uu____4224 =
                   (let uu____4227 = eq_tm t1 t2  in uu____4227 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4236 = eq_tm t11 t21  in
                             uu____4236 = Equal) w1 w2)
                    in
                 (if uu____4224 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4298)::a11,(b,uu____4301)::b1) ->
          let uu____4375 = eq_tm a b  in
          (match uu____4375 with
           | Equal  -> eq_args a11 b1
           | uu____4376 -> Unknown)
      | uu____4377 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4411) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4417,uu____4418) ->
        unrefine t2
    | uu____4459 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4465 =
      let uu____4466 = FStar_Syntax_Subst.compress t  in
      uu____4466.FStar_Syntax_Syntax.n  in
    match uu____4465 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4469 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4483) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4488 ->
        let uu____4505 =
          let uu____4506 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4506 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4505 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4568,uu____4569) ->
        is_uvar t1
    | uu____4610 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4616 =
      let uu____4617 = unrefine t  in uu____4617.FStar_Syntax_Syntax.n  in
    match uu____4616 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4622) -> is_unit t1
    | uu____4627 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4633 =
      let uu____4634 = unrefine t  in uu____4634.FStar_Syntax_Syntax.n  in
    match uu____4633 with
    | FStar_Syntax_Syntax.Tm_type uu____4637 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____4640) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4666) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____4671,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____4693 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____4699 =
      let uu____4700 = FStar_Syntax_Subst.compress e  in
      uu____4700.FStar_Syntax_Syntax.n  in
    match uu____4699 with
    | FStar_Syntax_Syntax.Tm_abs uu____4703 -> true
    | uu____4722 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4728 =
      let uu____4729 = FStar_Syntax_Subst.compress t  in
      uu____4729.FStar_Syntax_Syntax.n  in
    match uu____4728 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4732 -> true
    | uu____4747 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4755) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4761,uu____4762) ->
        pre_typ t2
    | uu____4803 -> t1
  
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
      let uu____4827 =
        let uu____4828 = un_uinst typ1  in uu____4828.FStar_Syntax_Syntax.n
         in
      match uu____4827 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____4893 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____4923 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____4943,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____4950) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____4955,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____4966,uu____4967,uu____4968,uu____4969,uu____4970) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____4980,uu____4981,uu____4982,uu____4983) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____4989,uu____4990,uu____4991,uu____4992,uu____4993) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____4999,uu____5000) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5002,uu____5003) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5006 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5007 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5008 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5021 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___117_5044  ->
    match uu___117_5044 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5057 'Auu____5058 .
    ('Auu____5057 FStar_Syntax_Syntax.syntax,'Auu____5058)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____5069  ->
    match uu____5069 with | (hd1,uu____5077) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5090 'Auu____5091 .
    ('Auu____5090 FStar_Syntax_Syntax.syntax,'Auu____5091)
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
      | uu____5188 ->
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
      let uu____5246 =
        FStar_List.map
          (fun uu____5273  ->
             match uu____5273 with
             | (bv,aq) ->
                 let uu____5292 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5292, aq)) bs
         in
      mk_app f uu____5246
  
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
          let uu____5341 = FStar_Ident.range_of_lid l  in
          let uu____5342 =
            let uu____5351 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5351  in
          uu____5342 FStar_Pervasives_Native.None uu____5341
      | uu____5359 ->
          let e =
            let uu____5373 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5373 args  in
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
  
let (mangle_field_name : FStar_Ident.ident -> FStar_Ident.ident) =
  fun x  ->
    FStar_Ident.mk_ident
      ((Prims.strcat "__fname__" x.FStar_Ident.idText),
        (x.FStar_Ident.idRange))
  
let (unmangle_field_name : FStar_Ident.ident -> FStar_Ident.ident) =
  fun x  ->
    if FStar_Util.starts_with x.FStar_Ident.idText "__fname__"
    then
      let uu____5388 =
        let uu____5393 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____5393, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____5388
    else x
  
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
      let j = unmangle_field_name i  in
      let jtext = j.FStar_Ident.idText  in
      let newi =
        if field_projector_contains_constructor jtext
        then j
        else
          FStar_Ident.mk_ident
            ((mk_field_projector_name_from_string
                (lid.FStar_Ident.ident).FStar_Ident.idText jtext),
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
          let uu____5444 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5444
          then
            let uu____5445 =
              let uu____5450 =
                let uu____5451 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____5451  in
              let uu____5452 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5450, uu____5452)  in
            FStar_Ident.mk_ident uu____5445
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___123_5455 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___123_5455.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___123_5455.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5456 = mk_field_projector_name_from_ident lid nm  in
        (uu____5456, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5467) -> ses
    | uu____5476 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____5485 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5496 = FStar_Syntax_Unionfind.find uv  in
      match uu____5496 with
      | FStar_Pervasives_Native.Some uu____5499 ->
          let uu____5500 =
            let uu____5501 =
              let uu____5502 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5502  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5501  in
          failwith uu____5500
      | uu____5503 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____5578 -> q1 = q2
  
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
              let uu____5623 =
                let uu___124_5624 = rc  in
                let uu____5625 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___124_5624.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____5625;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___124_5624.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____5623
           in
        match bs with
        | [] -> t
        | uu____5642 ->
            let body =
              let uu____5644 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____5644  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____5678 =
                   let uu____5685 =
                     let uu____5686 =
                       let uu____5705 =
                         let uu____5714 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____5714 bs'  in
                       let uu____5729 = close_lopt lopt'  in
                       (uu____5705, t1, uu____5729)  in
                     FStar_Syntax_Syntax.Tm_abs uu____5686  in
                   FStar_Syntax_Syntax.mk uu____5685  in
                 uu____5678 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____5747 ->
                 let uu____5754 =
                   let uu____5761 =
                     let uu____5762 =
                       let uu____5781 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____5790 = close_lopt lopt  in
                       (uu____5781, body, uu____5790)  in
                     FStar_Syntax_Syntax.Tm_abs uu____5762  in
                   FStar_Syntax_Syntax.mk uu____5761  in
                 uu____5754 FStar_Pervasives_Native.None
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
      | uu____5848 ->
          let uu____5857 =
            let uu____5864 =
              let uu____5865 =
                let uu____5880 = FStar_Syntax_Subst.close_binders bs  in
                let uu____5889 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____5880, uu____5889)  in
              FStar_Syntax_Syntax.Tm_arrow uu____5865  in
            FStar_Syntax_Syntax.mk uu____5864  in
          uu____5857 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
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
      let uu____5940 =
        let uu____5941 = FStar_Syntax_Subst.compress t  in
        uu____5941.FStar_Syntax_Syntax.n  in
      match uu____5940 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____5971) ->
               let uu____5980 =
                 let uu____5981 = FStar_Syntax_Subst.compress tres  in
                 uu____5981.FStar_Syntax_Syntax.n  in
               (match uu____5980 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6024 -> t)
           | uu____6025 -> t)
      | uu____6026 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6043 =
        let uu____6044 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6044 t.FStar_Syntax_Syntax.pos  in
      let uu____6045 =
        let uu____6052 =
          let uu____6053 =
            let uu____6060 =
              let uu____6063 =
                let uu____6064 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6064]  in
              FStar_Syntax_Subst.close uu____6063 t  in
            (b, uu____6060)  in
          FStar_Syntax_Syntax.Tm_refine uu____6053  in
        FStar_Syntax_Syntax.mk uu____6052  in
      uu____6045 FStar_Pervasives_Native.None uu____6043
  
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
        let uu____6145 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6145 with
         | (bs1,c1) ->
             let uu____6164 = is_total_comp c1  in
             if uu____6164
             then
               let uu____6177 = arrow_formals_comp (comp_result c1)  in
               (match uu____6177 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6243;
           FStar_Syntax_Syntax.index = uu____6244;
           FStar_Syntax_Syntax.sort = k2;_},uu____6246)
        -> arrow_formals_comp k2
    | uu____6253 ->
        let uu____6254 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6254)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                               FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____6288 = arrow_formals_comp k  in
    match uu____6288 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____6380 =
            let uu___125_6381 = rc  in
            let uu____6382 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___125_6381.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____6382;
              FStar_Syntax_Syntax.residual_flags =
                (uu___125_6381.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____6380
      | uu____6391 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____6425 =
        let uu____6426 =
          let uu____6429 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____6429  in
        uu____6426.FStar_Syntax_Syntax.n  in
      match uu____6425 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____6475 = aux t2 what  in
          (match uu____6475 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____6547 -> ([], t1, abs_body_lcomp)  in
    let uu____6564 = aux t FStar_Pervasives_Native.None  in
    match uu____6564 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____6612 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____6612 with
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
                    | (FStar_Pervasives_Native.None ,uu____6773) -> def
                    | (uu____6784,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____6796) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _0_4  -> FStar_Syntax_Syntax.U_name _0_4))
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
            let uu____6892 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____6892 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____6927 ->
            let t' = arrow binders c  in
            let uu____6939 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____6939 with
             | (uvs1,t'1) ->
                 let uu____6960 =
                   let uu____6961 = FStar_Syntax_Subst.compress t'1  in
                   uu____6961.FStar_Syntax_Syntax.n  in
                 (match uu____6960 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____7010 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____7031 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____7038 -> false
  
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
      let uu____7086 =
        let uu____7087 = pre_typ t  in uu____7087.FStar_Syntax_Syntax.n  in
      match uu____7086 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____7091 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____7102 =
        let uu____7103 = pre_typ t  in uu____7103.FStar_Syntax_Syntax.n  in
      match uu____7102 with
      | FStar_Syntax_Syntax.Tm_fvar uu____7106 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____7108) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____7134) ->
          is_constructed_typ t1 lid
      | uu____7139 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____7150 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____7151 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____7152 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____7154) -> get_tycon t2
    | uu____7179 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____7185 =
      let uu____7186 = un_uinst t  in uu____7186.FStar_Syntax_Syntax.n  in
    match uu____7185 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____7190 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____7197 =
        let uu____7200 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____7200  in
      match uu____7197 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____7213 -> false
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
  fun uu____7225  ->
    let u =
      let uu____7231 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_5  -> FStar_Syntax_Syntax.U_unif _0_5)
        uu____7231
       in
    let uu____7248 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____7248, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____7259 = eq_tm a a'  in
      match uu____7259 with | Equal  -> true | uu____7260 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____7263 =
    let uu____7270 =
      let uu____7271 =
        let uu____7272 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____7272
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____7271  in
    FStar_Syntax_Syntax.mk uu____7270  in
  uu____7263 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____7347 =
            let uu____7350 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____7351 =
              let uu____7358 =
                let uu____7359 =
                  let uu____7376 =
                    let uu____7387 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____7396 =
                      let uu____7407 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____7407]  in
                    uu____7387 :: uu____7396  in
                  (tand, uu____7376)  in
                FStar_Syntax_Syntax.Tm_app uu____7359  in
              FStar_Syntax_Syntax.mk uu____7358  in
            uu____7351 FStar_Pervasives_Native.None uu____7350  in
          FStar_Pervasives_Native.Some uu____7347
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____7486 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____7487 =
          let uu____7494 =
            let uu____7495 =
              let uu____7512 =
                let uu____7523 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____7532 =
                  let uu____7543 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____7543]  in
                uu____7523 :: uu____7532  in
              (op_t, uu____7512)  in
            FStar_Syntax_Syntax.Tm_app uu____7495  in
          FStar_Syntax_Syntax.mk uu____7494  in
        uu____7487 FStar_Pervasives_Native.None uu____7486
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____7602 =
      let uu____7609 =
        let uu____7610 =
          let uu____7627 =
            let uu____7638 = FStar_Syntax_Syntax.as_arg phi  in [uu____7638]
             in
          (t_not, uu____7627)  in
        FStar_Syntax_Syntax.Tm_app uu____7610  in
      FStar_Syntax_Syntax.mk uu____7609  in
    uu____7602 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____7831 =
      let uu____7838 =
        let uu____7839 =
          let uu____7856 =
            let uu____7867 = FStar_Syntax_Syntax.as_arg e  in [uu____7867]
             in
          (b2t_v, uu____7856)  in
        FStar_Syntax_Syntax.Tm_app uu____7839  in
      FStar_Syntax_Syntax.mk uu____7838  in
    uu____7831 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____7912 =
      let uu____7913 = unmeta t  in uu____7913.FStar_Syntax_Syntax.n  in
    match uu____7912 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____7917 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____7938 = is_t_true t1  in
      if uu____7938
      then t2
      else
        (let uu____7942 = is_t_true t2  in
         if uu____7942 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____7966 = is_t_true t1  in
      if uu____7966
      then t_true
      else
        (let uu____7970 = is_t_true t2  in
         if uu____7970 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____7994 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____7995 =
        let uu____8002 =
          let uu____8003 =
            let uu____8020 =
              let uu____8031 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____8040 =
                let uu____8051 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____8051]  in
              uu____8031 :: uu____8040  in
            (teq, uu____8020)  in
          FStar_Syntax_Syntax.Tm_app uu____8003  in
        FStar_Syntax_Syntax.mk uu____8002  in
      uu____7995 FStar_Pervasives_Native.None uu____7994
  
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
          let uu____8120 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____8121 =
            let uu____8128 =
              let uu____8129 =
                let uu____8146 =
                  let uu____8157 = FStar_Syntax_Syntax.iarg t  in
                  let uu____8166 =
                    let uu____8177 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____8186 =
                      let uu____8197 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____8197]  in
                    uu____8177 :: uu____8186  in
                  uu____8157 :: uu____8166  in
                (eq_inst, uu____8146)  in
              FStar_Syntax_Syntax.Tm_app uu____8129  in
            FStar_Syntax_Syntax.mk uu____8128  in
          uu____8121 FStar_Pervasives_Native.None uu____8120
  
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
        let uu____8276 =
          let uu____8283 =
            let uu____8284 =
              let uu____8301 =
                let uu____8312 = FStar_Syntax_Syntax.iarg t  in
                let uu____8321 =
                  let uu____8332 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____8341 =
                    let uu____8352 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____8352]  in
                  uu____8332 :: uu____8341  in
                uu____8312 :: uu____8321  in
              (t_has_type1, uu____8301)  in
            FStar_Syntax_Syntax.Tm_app uu____8284  in
          FStar_Syntax_Syntax.mk uu____8283  in
        uu____8276 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____8431 =
          let uu____8438 =
            let uu____8439 =
              let uu____8456 =
                let uu____8467 = FStar_Syntax_Syntax.iarg t  in
                let uu____8476 =
                  let uu____8487 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____8487]  in
                uu____8467 :: uu____8476  in
              (t_with_type1, uu____8456)  in
            FStar_Syntax_Syntax.Tm_app uu____8439  in
          FStar_Syntax_Syntax.mk uu____8438  in
        uu____8431 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____8535 =
    let uu____8542 =
      let uu____8543 =
        let uu____8550 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____8550, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____8543  in
    FStar_Syntax_Syntax.mk uu____8542  in
  uu____8535 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____8563 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____8576 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____8587 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____8563 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____8608  -> c0)
  
let (mk_residual_comp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.cflags Prims.list ->
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
        let uu____8686 =
          let uu____8693 =
            let uu____8694 =
              let uu____8711 =
                let uu____8722 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____8731 =
                  let uu____8742 =
                    let uu____8751 =
                      let uu____8752 =
                        let uu____8753 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____8753]  in
                      abs uu____8752 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____8751  in
                  [uu____8742]  in
                uu____8722 :: uu____8731  in
              (fa, uu____8711)  in
            FStar_Syntax_Syntax.Tm_app uu____8694  in
          FStar_Syntax_Syntax.mk uu____8693  in
        uu____8686 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____8880 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____8880
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____8893 -> true
    | uu____8894 -> false
  
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
          let uu____8939 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____8939, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____8967 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____8967, FStar_Pervasives_Native.None, t2)  in
        let uu____8980 =
          let uu____8981 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____8981  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____8980
  
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
      let uu____9055 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____9058 =
        let uu____9069 = FStar_Syntax_Syntax.as_arg p  in [uu____9069]  in
      mk_app uu____9055 uu____9058
  
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
      let uu____9107 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____9110 =
        let uu____9121 = FStar_Syntax_Syntax.as_arg p  in [uu____9121]  in
      mk_app uu____9107 uu____9110
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____9155 = head_and_args t  in
    match uu____9155 with
    | (head1,args) ->
        let uu____9202 =
          let uu____9217 =
            let uu____9218 = un_uinst head1  in
            uu____9218.FStar_Syntax_Syntax.n  in
          (uu____9217, args)  in
        (match uu____9202 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____9237)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____9303 =
                    let uu____9308 =
                      let uu____9309 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____9309]  in
                    FStar_Syntax_Subst.open_term uu____9308 p  in
                  (match uu____9303 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____9366 -> failwith "impossible"  in
                       let uu____9373 =
                         let uu____9374 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____9374
                          in
                       if uu____9373
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____9388 -> FStar_Pervasives_Native.None)
         | uu____9391 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____9421 = head_and_args t  in
    match uu____9421 with
    | (head1,args) ->
        let uu____9472 =
          let uu____9487 =
            let uu____9488 = FStar_Syntax_Subst.compress head1  in
            uu____9488.FStar_Syntax_Syntax.n  in
          (uu____9487, args)  in
        (match uu____9472 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____9510;
               FStar_Syntax_Syntax.vars = uu____9511;_},u::[]),(t1,uu____9514)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____9561 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____9595 = head_and_args t  in
    match uu____9595 with
    | (head1,args) ->
        let uu____9646 =
          let uu____9661 =
            let uu____9662 = FStar_Syntax_Subst.compress head1  in
            uu____9662.FStar_Syntax_Syntax.n  in
          (uu____9661, args)  in
        (match uu____9646 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____9684;
               FStar_Syntax_Syntax.vars = uu____9685;_},u::[]),(t1,uu____9688)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____9735 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9761 = let uu____9778 = unmeta t  in head_and_args uu____9778
       in
    match uu____9761 with
    | (head1,uu____9780) ->
        let uu____9805 =
          let uu____9806 = un_uinst head1  in
          uu____9806.FStar_Syntax_Syntax.n  in
        (match uu____9805 with
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
         | uu____9810 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____9828 =
      let uu____9841 =
        let uu____9842 = FStar_Syntax_Subst.compress t  in
        uu____9842.FStar_Syntax_Syntax.n  in
      match uu____9841 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____9971 =
            let uu____9982 =
              let uu____9983 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____9983  in
            (b, uu____9982)  in
          FStar_Pervasives_Native.Some uu____9971
      | uu____10000 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____9828
      (fun uu____10038  ->
         match uu____10038 with
         | (b,c) ->
             let uu____10075 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____10075 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____10138 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____10171 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____10171
  
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
    match projectee with | QAll _0 -> true | uu____10219 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____10257 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____10293 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____10330) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____10342) ->
          unmeta_monadic t
      | uu____10355 -> f2  in
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
      let aux f2 uu____10439 =
        match uu____10439 with
        | (lid,arity) ->
            let uu____10448 =
              let uu____10465 = unmeta_monadic f2  in
              head_and_args uu____10465  in
            (match uu____10448 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____10495 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____10495
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____10572 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____10572)
      | uu____10585 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____10646 = head_and_args t1  in
        match uu____10646 with
        | (t2,args) ->
            let uu____10701 = un_uinst t2  in
            let uu____10702 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____10743  ->
                      match uu____10743 with
                      | (t3,imp) ->
                          let uu____10762 = unascribe t3  in
                          (uu____10762, imp)))
               in
            (uu____10701, uu____10702)
         in
      let rec aux qopt out t1 =
        let uu____10811 = let uu____10834 = flat t1  in (qopt, uu____10834)
           in
        match uu____10811 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____10873;
                 FStar_Syntax_Syntax.vars = uu____10874;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____10877);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____10878;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____10879;_},uu____10880)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____10979;
                 FStar_Syntax_Syntax.vars = uu____10980;_},uu____10981::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____10984);
                  FStar_Syntax_Syntax.pos = uu____10985;
                  FStar_Syntax_Syntax.vars = uu____10986;_},uu____10987)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____11101;
               FStar_Syntax_Syntax.vars = uu____11102;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____11105);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____11106;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____11107;_},uu____11108)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____11199 =
              let uu____11202 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____11202  in
            aux uu____11199 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____11210;
               FStar_Syntax_Syntax.vars = uu____11211;_},uu____11212::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____11215);
                FStar_Syntax_Syntax.pos = uu____11216;
                FStar_Syntax_Syntax.vars = uu____11217;_},uu____11218)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____11325 =
              let uu____11328 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____11328  in
            aux uu____11325 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____11336) ->
            let bs = FStar_List.rev out  in
            let uu____11386 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____11386 with
             | (bs1,t2) ->
                 let uu____11395 = patterns t2  in
                 (match uu____11395 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____11443 -> FStar_Pervasives_Native.None  in
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
      let uu____11519 = un_squash t  in
      FStar_Util.bind_opt uu____11519
        (fun t1  ->
           let uu____11535 = head_and_args' t1  in
           match uu____11535 with
           | (hd1,args) ->
               let uu____11574 =
                 let uu____11579 =
                   let uu____11580 = un_uinst hd1  in
                   uu____11580.FStar_Syntax_Syntax.n  in
                 (uu____11579, (FStar_List.length args))  in
               (match uu____11574 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_6) when
                    (_0_6 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_7) when
                    (_0_7 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_8) when
                    (_0_8 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_9) when
                    (_0_9 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_10) when
                    (_0_10 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_11) when
                    (_0_11 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_12) when
                    (_0_12 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_13) when
                    (_0_13 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____11601 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____11630 = un_squash t  in
      FStar_Util.bind_opt uu____11630
        (fun t1  ->
           let uu____11645 = arrow_one t1  in
           match uu____11645 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____11660 =
                 let uu____11661 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____11661  in
               if uu____11660
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____11668 = comp_to_comp_typ_nouniv c  in
                    uu____11668.FStar_Syntax_Syntax.result_typ  in
                  let uu____11669 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____11669
                  then
                    let uu____11674 = patterns q  in
                    match uu____11674 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____11736 =
                       let uu____11737 =
                         let uu____11742 =
                           let uu____11743 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____11754 =
                             let uu____11765 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____11765]  in
                           uu____11743 :: uu____11754  in
                         (FStar_Parser_Const.imp_lid, uu____11742)  in
                       BaseConn uu____11737  in
                     FStar_Pervasives_Native.Some uu____11736))
           | uu____11798 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____11806 = un_squash t  in
      FStar_Util.bind_opt uu____11806
        (fun t1  ->
           let uu____11837 = head_and_args' t1  in
           match uu____11837 with
           | (hd1,args) ->
               let uu____11876 =
                 let uu____11891 =
                   let uu____11892 = un_uinst hd1  in
                   uu____11892.FStar_Syntax_Syntax.n  in
                 (uu____11891, args)  in
               (match uu____11876 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____11909)::(a2,uu____11911)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____11962 =
                      let uu____11963 = FStar_Syntax_Subst.compress a2  in
                      uu____11963.FStar_Syntax_Syntax.n  in
                    (match uu____11962 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____11970) ->
                         let uu____12005 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____12005 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____12058 -> failwith "impossible"  in
                              let uu____12065 = patterns q1  in
                              (match uu____12065 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____12126 -> FStar_Pervasives_Native.None)
                | uu____12127 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____12150 = destruct_sq_forall phi  in
          (match uu____12150 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____12166 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____12172 = destruct_sq_exists phi  in
          (match uu____12172 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____12188 -> f1)
      | uu____12191 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____12195 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____12195
      (fun uu____12200  ->
         let uu____12201 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____12201
           (fun uu____12206  ->
              let uu____12207 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____12207
                (fun uu____12212  ->
                   let uu____12213 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____12213
                     (fun uu____12218  ->
                        let uu____12219 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____12219
                          (fun uu____12223  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____12235 =
      let uu____12236 = FStar_Syntax_Subst.compress t  in
      uu____12236.FStar_Syntax_Syntax.n  in
    match uu____12235 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____12243) ->
        let uu____12278 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____12278 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____12312 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____12312
             then
               let uu____12317 =
                 let uu____12328 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____12328]  in
               mk_app t uu____12317
             else e1)
    | uu____12354 ->
        let uu____12355 =
          let uu____12366 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____12366]  in
        mk_app t uu____12355
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____12407 =
            let uu____12412 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____12412  in
          let uu____12413 =
            let uu____12414 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____12414  in
          let uu____12417 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____12407 a.FStar_Syntax_Syntax.action_univs uu____12413
            FStar_Parser_Const.effect_Tot_lid uu____12417 [] pos
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
    let uu____12440 =
      let uu____12447 =
        let uu____12448 =
          let uu____12465 =
            let uu____12476 = FStar_Syntax_Syntax.as_arg t  in [uu____12476]
             in
          (reify_1, uu____12465)  in
        FStar_Syntax_Syntax.Tm_app uu____12448  in
      FStar_Syntax_Syntax.mk uu____12447  in
    uu____12440 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____12522 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____12546 = unfold_lazy i  in delta_qualifier uu____12546
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____12548 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____12549 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____12550 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____12573 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____12586 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____12587 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____12594 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____12595 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____12611) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____12616;
           FStar_Syntax_Syntax.index = uu____12617;
           FStar_Syntax_Syntax.sort = t2;_},uu____12619)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____12627) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____12633,uu____12634) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____12676) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____12701,t2,uu____12703) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____12728,t2) -> delta_qualifier t2
  
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
    let uu____12759 = delta_qualifier t  in incr_delta_depth uu____12759
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____12765 =
      let uu____12766 = FStar_Syntax_Subst.compress t  in
      uu____12766.FStar_Syntax_Syntax.n  in
    match uu____12765 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____12769 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____12783 =
      let uu____12800 = unmeta e  in head_and_args uu____12800  in
    match uu____12783 with
    | (head1,args) ->
        let uu____12831 =
          let uu____12846 =
            let uu____12847 = un_uinst head1  in
            uu____12847.FStar_Syntax_Syntax.n  in
          (uu____12846, args)  in
        (match uu____12831 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12865) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____12889::(hd1,uu____12891)::(tl1,uu____12893)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____12960 =
               let uu____12963 =
                 let uu____12966 = list_elements tl1  in
                 FStar_Util.must uu____12966  in
               hd1 :: uu____12963  in
             FStar_Pervasives_Native.Some uu____12960
         | uu____12975 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____12998 .
    ('Auu____12998 -> 'Auu____12998) ->
      'Auu____12998 Prims.list -> 'Auu____12998 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____13023 = f a  in [uu____13023]
      | x::xs -> let uu____13028 = apply_last f xs  in x :: uu____13028
  
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
          let uu____13074 =
            let uu____13081 =
              let uu____13082 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____13082  in
            FStar_Syntax_Syntax.mk uu____13081  in
          uu____13074 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____13099 =
            let uu____13104 =
              let uu____13105 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____13105
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____13104 args  in
          uu____13099 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____13121 =
            let uu____13126 =
              let uu____13127 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____13127
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____13126 args  in
          uu____13121 FStar_Pervasives_Native.None pos  in
        let uu____13130 =
          let uu____13131 =
            let uu____13132 = FStar_Syntax_Syntax.iarg typ  in [uu____13132]
             in
          nil uu____13131 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____13166 =
                 let uu____13167 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____13176 =
                   let uu____13187 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____13196 =
                     let uu____13207 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____13207]  in
                   uu____13187 :: uu____13196  in
                 uu____13167 :: uu____13176  in
               cons1 uu____13166 t.FStar_Syntax_Syntax.pos) l uu____13130
  
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
        | uu____13311 -> false
  
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
          | uu____13418 -> false
  
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
        | uu____13573 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____13607 = FStar_ST.op_Bang debug_term_eq  in
          if uu____13607
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
        let t11 = let uu____13799 = unmeta_safe t1  in canon_app uu____13799
           in
        let t21 = let uu____13805 = unmeta_safe t2  in canon_app uu____13805
           in
        let uu____13808 =
          let uu____13813 =
            let uu____13814 =
              let uu____13817 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____13817  in
            uu____13814.FStar_Syntax_Syntax.n  in
          let uu____13818 =
            let uu____13819 =
              let uu____13822 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____13822  in
            uu____13819.FStar_Syntax_Syntax.n  in
          (uu____13813, uu____13818)  in
        match uu____13808 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____13823,uu____13824) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____13831,FStar_Syntax_Syntax.Tm_uinst uu____13832) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____13839,uu____13840) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____13863,FStar_Syntax_Syntax.Tm_delayed uu____13864) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____13887,uu____13888) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____13915,FStar_Syntax_Syntax.Tm_ascribed uu____13916) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____13949 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____13949
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____13952 = FStar_Const.eq_const c1 c2  in
            check "const" uu____13952
        | (FStar_Syntax_Syntax.Tm_type
           uu____13953,FStar_Syntax_Syntax.Tm_type uu____13954) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____14011 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____14011) &&
              (let uu____14019 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____14019)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____14066 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____14066) &&
              (let uu____14074 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____14074)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____14088 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____14088)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____14143 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____14143) &&
              (let uu____14145 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____14145)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____14232 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____14232) &&
              (let uu____14234 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____14234)
        | (FStar_Syntax_Syntax.Tm_lazy uu____14249,uu____14250) ->
            let uu____14251 =
              let uu____14252 = unlazy t11  in
              term_eq_dbg dbg uu____14252 t21  in
            check "lazy_l" uu____14251
        | (uu____14253,FStar_Syntax_Syntax.Tm_lazy uu____14254) ->
            let uu____14255 =
              let uu____14256 = unlazy t21  in
              term_eq_dbg dbg t11 uu____14256  in
            check "lazy_r" uu____14255
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____14292 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____14292))
              &&
              (let uu____14294 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____14294)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____14296),FStar_Syntax_Syntax.Tm_uvar (u2,uu____14298)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____14355 =
               let uu____14356 = eq_quoteinfo qi1 qi2  in uu____14356 = Equal
                in
             check "tm_quoted qi" uu____14355) &&
              (let uu____14358 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____14358)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____14385 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____14385) &&
                   (let uu____14387 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____14387)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____14404 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____14404) &&
                    (let uu____14406 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____14406))
                   &&
                   (let uu____14408 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____14408)
             | uu____14409 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____14414) -> fail "unk"
        | (uu____14415,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____14416,uu____14417) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____14418,uu____14419) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____14420,uu____14421) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____14422,uu____14423) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____14424,uu____14425) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____14426,uu____14427) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____14446,uu____14447) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____14462,uu____14463) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____14470,uu____14471) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____14488,uu____14489) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____14512,uu____14513) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____14526,uu____14527) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____14540,uu____14541) ->
            fail "bottom"
        | (uu____14548,FStar_Syntax_Syntax.Tm_bvar uu____14549) ->
            fail "bottom"
        | (uu____14550,FStar_Syntax_Syntax.Tm_name uu____14551) ->
            fail "bottom"
        | (uu____14552,FStar_Syntax_Syntax.Tm_fvar uu____14553) ->
            fail "bottom"
        | (uu____14554,FStar_Syntax_Syntax.Tm_constant uu____14555) ->
            fail "bottom"
        | (uu____14556,FStar_Syntax_Syntax.Tm_type uu____14557) ->
            fail "bottom"
        | (uu____14558,FStar_Syntax_Syntax.Tm_abs uu____14559) ->
            fail "bottom"
        | (uu____14578,FStar_Syntax_Syntax.Tm_arrow uu____14579) ->
            fail "bottom"
        | (uu____14594,FStar_Syntax_Syntax.Tm_refine uu____14595) ->
            fail "bottom"
        | (uu____14602,FStar_Syntax_Syntax.Tm_app uu____14603) ->
            fail "bottom"
        | (uu____14620,FStar_Syntax_Syntax.Tm_match uu____14621) ->
            fail "bottom"
        | (uu____14644,FStar_Syntax_Syntax.Tm_let uu____14645) ->
            fail "bottom"
        | (uu____14658,FStar_Syntax_Syntax.Tm_uvar uu____14659) ->
            fail "bottom"
        | (uu____14672,FStar_Syntax_Syntax.Tm_meta uu____14673) ->
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
               let uu____14706 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____14706)
          (fun q1  ->
             fun q2  ->
               let uu____14716 =
                 let uu____14717 = eq_aqual q1 q2  in uu____14717 = Equal  in
               check "arg qual" uu____14716) a1 a2

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
               let uu____14740 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____14740)
          (fun q1  ->
             fun q2  ->
               let uu____14750 =
                 let uu____14751 = eq_aqual q1 q2  in uu____14751 = Equal  in
               check "binder qual" uu____14750) b1 b2

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
        ((let uu____14767 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____14767) &&
           (let uu____14769 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____14769))
          && true

and (eq_flags_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.cflags -> FStar_Syntax_Syntax.cflags -> Prims.bool)
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
    fun uu____14774  ->
      fun uu____14775  ->
        match (uu____14774, uu____14775) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____14900 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____14900) &&
               (let uu____14902 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____14902))
              &&
              (let uu____14904 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____14943 -> false  in
               check "branch when" uu____14904)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____14961 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____14961) &&
           (let uu____14967 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____14967))
          &&
          (let uu____14969 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____14969)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____14981 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____14981 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____15026 ->
        let uu____15049 =
          let uu____15050 = FStar_Syntax_Subst.compress t  in
          sizeof uu____15050  in
        (Prims.parse_int "1") + uu____15049
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____15052 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____15052
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____15054 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____15054
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____15061 = sizeof t1  in (FStar_List.length us) + uu____15061
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____15064) ->
        let uu____15089 = sizeof t1  in
        let uu____15090 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____15103  ->
                 match uu____15103 with
                 | (bv,uu____15111) ->
                     let uu____15116 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____15116) (Prims.parse_int "0") bs
           in
        uu____15089 + uu____15090
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____15143 = sizeof hd1  in
        let uu____15144 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____15157  ->
                 match uu____15157 with
                 | (arg,uu____15165) ->
                     let uu____15170 = sizeof arg  in acc + uu____15170)
            (Prims.parse_int "0") args
           in
        uu____15143 + uu____15144
    | uu____15171 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____15182 =
        let uu____15183 = un_uinst t  in uu____15183.FStar_Syntax_Syntax.n
         in
      match uu____15182 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____15187 -> false
  
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
        let uu____15228 = FStar_Options.set_options t s  in
        match uu____15228 with
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
          ((let uu____15236 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____15236 (fun a235  -> ()));
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
      | FStar_Syntax_Syntax.PushOptions sopt ->
          (FStar_Options.push ();
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
      | FStar_Syntax_Syntax.PopOptions  -> FStar_Options.pop ()
  
let rec (unbound_variables :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun tm  ->
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____15267 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____15293 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____15308 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____15309 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____15310 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____15319) ->
        let uu____15344 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____15344 with
         | (bs1,t2) ->
             let uu____15353 =
               FStar_List.collect
                 (fun uu____15365  ->
                    match uu____15365 with
                    | (b,uu____15375) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____15380 = unbound_variables t2  in
             FStar_List.append uu____15353 uu____15380)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____15405 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____15405 with
         | (bs1,c1) ->
             let uu____15414 =
               FStar_List.collect
                 (fun uu____15426  ->
                    match uu____15426 with
                    | (b,uu____15436) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____15441 = unbound_variables_comp c1  in
             FStar_List.append uu____15414 uu____15441)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____15450 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____15450 with
         | (bs,t2) ->
             let uu____15473 =
               FStar_List.collect
                 (fun uu____15485  ->
                    match uu____15485 with
                    | (b1,uu____15495) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____15500 = unbound_variables t2  in
             FStar_List.append uu____15473 uu____15500)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____15529 =
          FStar_List.collect
            (fun uu____15543  ->
               match uu____15543 with
               | (x,uu____15555) -> unbound_variables x) args
           in
        let uu____15564 = unbound_variables t1  in
        FStar_List.append uu____15529 uu____15564
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____15605 = unbound_variables t1  in
        let uu____15608 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____15623 = FStar_Syntax_Subst.open_branch br  in
                  match uu____15623 with
                  | (p,wopt,t2) ->
                      let uu____15645 = unbound_variables t2  in
                      let uu____15648 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____15645 uu____15648))
           in
        FStar_List.append uu____15605 uu____15608
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____15662) ->
        let uu____15703 = unbound_variables t1  in
        let uu____15706 =
          let uu____15709 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____15740 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____15709 uu____15740  in
        FStar_List.append uu____15703 uu____15706
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____15778 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____15781 =
          let uu____15784 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____15787 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____15792 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____15794 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____15794 with
                 | (uu____15815,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____15784 uu____15787  in
        FStar_List.append uu____15778 uu____15781
    | FStar_Syntax_Syntax.Tm_let ((uu____15817,lbs),t1) ->
        let uu____15834 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____15834 with
         | (lbs1,t2) ->
             let uu____15849 = unbound_variables t2  in
             let uu____15852 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____15859 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____15862 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____15859 uu____15862) lbs1
                in
             FStar_List.append uu____15849 uu____15852)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____15879 = unbound_variables t1  in
        let uu____15882 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____15921  ->
                      match uu____15921 with
                      | (a,uu____15933) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____15942,uu____15943,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____15949,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____15955 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____15962 -> []
          | FStar_Syntax_Syntax.Meta_named uu____15963 -> []  in
        FStar_List.append uu____15879 uu____15882

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____15970) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____15980) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____15990 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____15993 =
          FStar_List.collect
            (fun uu____16007  ->
               match uu____16007 with
               | (a,uu____16019) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____15990 uu____15993
