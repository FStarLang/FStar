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
    FStar_Syntax_Syntax.cflag Prims.list)
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
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    fun f  ->
      let uu___125_1448 = c  in
      let uu____1449 =
        let uu____1450 =
          let uu___126_1451 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___126_1451.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___126_1451.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___126_1451.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___126_1451.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1450  in
      {
        FStar_Syntax_Syntax.n = uu____1449;
        FStar_Syntax_Syntax.pos = (uu___125_1448.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___125_1448.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1476 -> c
        | FStar_Syntax_Syntax.GTotal uu____1485 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___127_1496 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___127_1496.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___127_1496.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___127_1496.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___127_1496.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___128_1497 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___128_1497.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___128_1497.FStar_Syntax_Syntax.vars)
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
            (fun uu___112_1581  ->
               match uu___112_1581 with
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
            (fun uu___113_1591  ->
               match uu___113_1591 with
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
            (fun uu___114_1601  ->
               match uu___114_1601 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1602 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___115_1615  ->
            match uu___115_1615 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1616 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___116_1625  ->
            match uu___116_1625 with
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
                (fun uu___117_1672  ->
                   match uu___117_1672 with
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
            (fun uu___118_1706  ->
               match uu___118_1706 with
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
                (fun uu___119_2367  ->
                   match uu___119_2367 with
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
            (let uu___129_2443 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___129_2443.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___129_2443.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___129_2443.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___129_2443.FStar_Syntax_Syntax.flags)
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
         (fun uu___120_2472  ->
            match uu___120_2472 with
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
      | (FStar_Syntax_Syntax.Lazy_goal ,FStar_Syntax_Syntax.Lazy_goal ) ->
          true
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
let (eq_inj : eq_result -> eq_result -> eq_result) =
  fun f  ->
    fun g  ->
      match (f, g) with
      | (Equal ,Equal ) -> Equal
      | (NotEqual ,uu____2959) -> NotEqual
      | (uu____2960,NotEqual ) -> NotEqual
      | (Unknown ,uu____2961) -> Unknown
      | (uu____2962,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___121_3080 = if uu___121_3080 then Equal else Unknown
         in
      let equal_iff uu___122_3087 = if uu___122_3087 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____3105 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3127 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3127
        then
          let uu____3129 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3206  ->
                    match uu____3206 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3247 = eq_tm a1 a2  in
                        eq_inj acc uu____3247) Equal) uu____3129
        else NotEqual  in
      let uu____3249 =
        let uu____3254 =
          let uu____3255 = unmeta t11  in uu____3255.FStar_Syntax_Syntax.n
           in
        let uu____3258 =
          let uu____3259 = unmeta t21  in uu____3259.FStar_Syntax_Syntax.n
           in
        (uu____3254, uu____3258)  in
      match uu____3249 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3264,uu____3265) ->
          let uu____3266 = unlazy t11  in eq_tm uu____3266 t21
      | (uu____3267,FStar_Syntax_Syntax.Tm_lazy uu____3268) ->
          let uu____3269 = unlazy t21  in eq_tm t11 uu____3269
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
            (let uu____3295 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____3295)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3308 = eq_tm f g  in
          eq_and uu____3308
            (fun uu____3311  ->
               let uu____3312 = eq_univs_list us vs  in equal_if uu____3312)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3313),uu____3314) -> Unknown
      | (uu____3315,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3316)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3319 = FStar_Const.eq_const c d  in equal_iff uu____3319
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3321)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3323))) ->
          let uu____3352 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3352
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3405 =
            let uu____3410 =
              let uu____3411 = un_uinst h1  in
              uu____3411.FStar_Syntax_Syntax.n  in
            let uu____3414 =
              let uu____3415 = un_uinst h2  in
              uu____3415.FStar_Syntax_Syntax.n  in
            (uu____3410, uu____3414)  in
          (match uu____3405 with
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
                 (let uu____3427 =
                    let uu____3428 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3428  in
                  FStar_List.mem uu____3427 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3429 ->
               let uu____3434 = eq_tm h1 h2  in
               eq_and uu____3434 (fun uu____3436  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3541 = FStar_List.zip bs1 bs2  in
            let uu____3604 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3641  ->
                 fun a  ->
                   match uu____3641 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3734  -> branch_matches b1 b2))
              uu____3541 uu____3604
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3738 = eq_univs u v1  in equal_if uu____3738
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____3751 = eq_quoteinfo q1 q2  in
          eq_and uu____3751 (fun uu____3753  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____3766 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____3766 (fun uu____3768  -> eq_tm phi1 phi2)
      | uu____3769 -> Unknown

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
      | ([],uu____3839) -> NotEqual
      | (uu____3870,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____3960 = eq_tm t1 t2  in
             match uu____3960 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____3961 = eq_antiquotes a11 a21  in
                 (match uu____3961 with
                  | NotEqual  -> NotEqual
                  | uu____3962 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____3977) -> NotEqual
      | (uu____3984,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4011 -> NotEqual

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
        | (uu____4098,uu____4099) -> false  in
      let uu____4108 = b1  in
      match uu____4108 with
      | (p1,w1,t1) ->
          let uu____4142 = b2  in
          (match uu____4142 with
           | (p2,w2,t2) ->
               let uu____4176 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4176
               then
                 let uu____4177 =
                   (let uu____4180 = eq_tm t1 t2  in uu____4180 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4189 = eq_tm t11 t21  in
                             uu____4189 = Equal) w1 w2)
                    in
                 (if uu____4177 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4251)::a11,(b,uu____4254)::b1) ->
          let uu____4328 = eq_tm a b  in
          (match uu____4328 with
           | Equal  -> eq_args a11 b1
           | uu____4329 -> Unknown)
      | uu____4330 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4364) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4370,uu____4371) ->
        unrefine t2
    | uu____4412 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4418 =
      let uu____4419 = FStar_Syntax_Subst.compress t  in
      uu____4419.FStar_Syntax_Syntax.n  in
    match uu____4418 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4422 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4436) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4441 ->
        let uu____4458 =
          let uu____4459 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4459 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4458 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4521,uu____4522) ->
        is_uvar t1
    | uu____4563 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4569 =
      let uu____4570 = unrefine t  in uu____4570.FStar_Syntax_Syntax.n  in
    match uu____4569 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4575) -> is_unit t1
    | uu____4580 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4586 =
      let uu____4587 = FStar_Syntax_Subst.compress t  in
      uu____4587.FStar_Syntax_Syntax.n  in
    match uu____4586 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____4591 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4597 =
      let uu____4598 = unrefine t  in uu____4598.FStar_Syntax_Syntax.n  in
    match uu____4597 with
    | FStar_Syntax_Syntax.Tm_type uu____4601 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____4604) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4630) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____4635,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____4657 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____4663 =
      let uu____4664 = FStar_Syntax_Subst.compress e  in
      uu____4664.FStar_Syntax_Syntax.n  in
    match uu____4663 with
    | FStar_Syntax_Syntax.Tm_abs uu____4667 -> true
    | uu____4686 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4692 =
      let uu____4693 = FStar_Syntax_Subst.compress t  in
      uu____4693.FStar_Syntax_Syntax.n  in
    match uu____4692 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4696 -> true
    | uu____4711 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4719) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4725,uu____4726) ->
        pre_typ t2
    | uu____4767 -> t1
  
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
      let uu____4791 =
        let uu____4792 = un_uinst typ1  in uu____4792.FStar_Syntax_Syntax.n
         in
      match uu____4791 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____4857 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____4887 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____4907,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____4914) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____4919,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____4930,uu____4931,uu____4932,uu____4933,uu____4934) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____4944,uu____4945,uu____4946,uu____4947) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____4953,uu____4954,uu____4955,uu____4956,uu____4957) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____4963,uu____4964) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4966,uu____4967) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____4970 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____4971 -> []
    | FStar_Syntax_Syntax.Sig_main uu____4972 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____4985 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___123_5008  ->
    match uu___123_5008 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5021 'Auu____5022 .
    ('Auu____5021 FStar_Syntax_Syntax.syntax,'Auu____5022)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____5033  ->
    match uu____5033 with | (hd1,uu____5041) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5054 'Auu____5055 .
    ('Auu____5054 FStar_Syntax_Syntax.syntax,'Auu____5055)
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
      | uu____5152 ->
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
      let uu____5210 =
        FStar_List.map
          (fun uu____5237  ->
             match uu____5237 with
             | (bv,aq) ->
                 let uu____5256 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5256, aq)) bs
         in
      mk_app f uu____5210
  
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
          let uu____5305 = FStar_Ident.range_of_lid l  in
          let uu____5306 =
            let uu____5315 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5315  in
          uu____5306 FStar_Pervasives_Native.None uu____5305
      | uu____5323 ->
          let e =
            let uu____5337 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5337 args  in
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
          let uu____5390 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5390
          then
            let uu____5391 =
              let uu____5396 =
                let uu____5397 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____5397  in
              let uu____5398 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5396, uu____5398)  in
            FStar_Ident.mk_ident uu____5391
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___130_5401 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___130_5401.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___130_5401.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5402 = mk_field_projector_name_from_ident lid nm  in
        (uu____5402, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5413) -> ses
    | uu____5422 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____5431 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5442 = FStar_Syntax_Unionfind.find uv  in
      match uu____5442 with
      | FStar_Pervasives_Native.Some uu____5445 ->
          let uu____5446 =
            let uu____5447 =
              let uu____5448 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5448  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5447  in
          failwith uu____5446
      | uu____5449 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____5524 -> q1 = q2
  
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
              let uu____5569 =
                let uu___131_5570 = rc  in
                let uu____5571 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___131_5570.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____5571;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___131_5570.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____5569
           in
        match bs with
        | [] -> t
        | uu____5588 ->
            let body =
              let uu____5590 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____5590  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____5620 =
                   let uu____5627 =
                     let uu____5628 =
                       let uu____5647 =
                         let uu____5656 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____5656 bs'  in
                       let uu____5671 = close_lopt lopt'  in
                       (uu____5647, t1, uu____5671)  in
                     FStar_Syntax_Syntax.Tm_abs uu____5628  in
                   FStar_Syntax_Syntax.mk uu____5627  in
                 uu____5620 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____5689 ->
                 let uu____5690 =
                   let uu____5697 =
                     let uu____5698 =
                       let uu____5717 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____5726 = close_lopt lopt  in
                       (uu____5717, body, uu____5726)  in
                     FStar_Syntax_Syntax.Tm_abs uu____5698  in
                   FStar_Syntax_Syntax.mk uu____5697  in
                 uu____5690 FStar_Pervasives_Native.None
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
      | uu____5784 ->
          let uu____5793 =
            let uu____5800 =
              let uu____5801 =
                let uu____5816 = FStar_Syntax_Subst.close_binders bs  in
                let uu____5825 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____5816, uu____5825)  in
              FStar_Syntax_Syntax.Tm_arrow uu____5801  in
            FStar_Syntax_Syntax.mk uu____5800  in
          uu____5793 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
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
      let uu____5876 =
        let uu____5877 = FStar_Syntax_Subst.compress t  in
        uu____5877.FStar_Syntax_Syntax.n  in
      match uu____5876 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____5907) ->
               let uu____5916 =
                 let uu____5917 = FStar_Syntax_Subst.compress tres  in
                 uu____5917.FStar_Syntax_Syntax.n  in
               (match uu____5916 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____5960 -> t)
           | uu____5961 -> t)
      | uu____5962 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____5979 =
        let uu____5980 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____5980 t.FStar_Syntax_Syntax.pos  in
      let uu____5981 =
        let uu____5988 =
          let uu____5989 =
            let uu____5996 =
              let uu____5999 =
                let uu____6000 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6000]  in
              FStar_Syntax_Subst.close uu____5999 t  in
            (b, uu____5996)  in
          FStar_Syntax_Syntax.Tm_refine uu____5989  in
        FStar_Syntax_Syntax.mk uu____5988  in
      uu____5981 FStar_Pervasives_Native.None uu____5979
  
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
        let uu____6081 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6081 with
         | (bs1,c1) ->
             let uu____6100 = is_total_comp c1  in
             if uu____6100
             then
               let uu____6113 = arrow_formals_comp (comp_result c1)  in
               (match uu____6113 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6179;
           FStar_Syntax_Syntax.index = uu____6180;
           FStar_Syntax_Syntax.sort = s;_},uu____6182)
        ->
        let rec aux s1 k2 =
          let uu____6212 =
            let uu____6213 = FStar_Syntax_Subst.compress s1  in
            uu____6213.FStar_Syntax_Syntax.n  in
          match uu____6212 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6228 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6243;
                 FStar_Syntax_Syntax.index = uu____6244;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6246)
              -> aux s2 k2
          | uu____6253 ->
              let uu____6254 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6254)
           in
        aux s k1
    | uu____6269 ->
        let uu____6270 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6270)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                               FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____6304 = arrow_formals_comp k  in
    match uu____6304 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____6441 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6441 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6465 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___124_6474  ->
                         match uu___124_6474 with
                         | FStar_Syntax_Syntax.DECREASES uu____6475 -> true
                         | uu____6478 -> false))
                  in
               (match uu____6465 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____6512 ->
                    let uu____6515 = is_total_comp c1  in
                    if uu____6515
                    then
                      let uu____6532 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____6532 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6624;
             FStar_Syntax_Syntax.index = uu____6625;
             FStar_Syntax_Syntax.sort = k2;_},uu____6627)
          -> arrow_until_decreases k2
      | uu____6634 -> ([], FStar_Pervasives_Native.None)  in
    let uu____6655 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____6655 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____6707 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____6726 =
                 FStar_Common.tabulate n_univs (fun uu____6734  -> false)  in
               let uu____6735 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____6757  ->
                         match uu____6757 with
                         | (x,uu____6765) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____6726 uu____6735)
           in
        ((n_univs + (FStar_List.length bs)), uu____6707)
  
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
          let uu____6823 =
            let uu___132_6824 = rc  in
            let uu____6825 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___132_6824.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____6825;
              FStar_Syntax_Syntax.residual_flags =
                (uu___132_6824.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____6823
      | uu____6834 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____6868 =
        let uu____6869 =
          let uu____6872 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____6872  in
        uu____6869.FStar_Syntax_Syntax.n  in
      match uu____6868 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____6918 = aux t2 what  in
          (match uu____6918 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____6990 -> ([], t1, abs_body_lcomp)  in
    let uu____7007 = aux t FStar_Pervasives_Native.None  in
    match uu____7007 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7055 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7055 with
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
                    | (FStar_Pervasives_Native.None ,uu____7216) -> def
                    | (uu____7227,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7239) ->
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
            let uu____7335 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7335 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7370 ->
            let t' = arrow binders c  in
            let uu____7382 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____7382 with
             | (uvs1,t'1) ->
                 let uu____7403 =
                   let uu____7404 = FStar_Syntax_Subst.compress t'1  in
                   uu____7404.FStar_Syntax_Syntax.n  in
                 (match uu____7403 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____7453 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____7474 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____7481 -> false
  
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
      let uu____7529 =
        let uu____7530 = pre_typ t  in uu____7530.FStar_Syntax_Syntax.n  in
      match uu____7529 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____7534 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____7545 =
        let uu____7546 = pre_typ t  in uu____7546.FStar_Syntax_Syntax.n  in
      match uu____7545 with
      | FStar_Syntax_Syntax.Tm_fvar uu____7549 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____7551) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____7577) ->
          is_constructed_typ t1 lid
      | uu____7582 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____7593 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____7594 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____7595 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____7597) -> get_tycon t2
    | uu____7622 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____7628 =
      let uu____7629 = un_uinst t  in uu____7629.FStar_Syntax_Syntax.n  in
    match uu____7628 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____7633 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____7640 =
        let uu____7643 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____7643  in
      match uu____7640 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____7656 -> false
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
  fun uu____7668  ->
    let u =
      let uu____7674 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_2  -> FStar_Syntax_Syntax.U_unif _0_2)
        uu____7674
       in
    let uu____7691 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____7691, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____7702 = eq_tm a a'  in
      match uu____7702 with | Equal  -> true | uu____7703 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____7706 =
    let uu____7713 =
      let uu____7714 =
        let uu____7715 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____7715
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____7714  in
    FStar_Syntax_Syntax.mk uu____7713  in
  uu____7706 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____7790 =
            let uu____7793 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____7794 =
              let uu____7801 =
                let uu____7802 =
                  let uu____7819 =
                    let uu____7830 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____7839 =
                      let uu____7850 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____7850]  in
                    uu____7830 :: uu____7839  in
                  (tand, uu____7819)  in
                FStar_Syntax_Syntax.Tm_app uu____7802  in
              FStar_Syntax_Syntax.mk uu____7801  in
            uu____7794 FStar_Pervasives_Native.None uu____7793  in
          FStar_Pervasives_Native.Some uu____7790
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____7929 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____7930 =
          let uu____7937 =
            let uu____7938 =
              let uu____7955 =
                let uu____7966 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____7975 =
                  let uu____7986 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____7986]  in
                uu____7966 :: uu____7975  in
              (op_t, uu____7955)  in
            FStar_Syntax_Syntax.Tm_app uu____7938  in
          FStar_Syntax_Syntax.mk uu____7937  in
        uu____7930 FStar_Pervasives_Native.None uu____7929
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8045 =
      let uu____8052 =
        let uu____8053 =
          let uu____8070 =
            let uu____8081 = FStar_Syntax_Syntax.as_arg phi  in [uu____8081]
             in
          (t_not, uu____8070)  in
        FStar_Syntax_Syntax.Tm_app uu____8053  in
      FStar_Syntax_Syntax.mk uu____8052  in
    uu____8045 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____8274 =
      let uu____8281 =
        let uu____8282 =
          let uu____8299 =
            let uu____8310 = FStar_Syntax_Syntax.as_arg e  in [uu____8310]
             in
          (b2t_v, uu____8299)  in
        FStar_Syntax_Syntax.Tm_app uu____8282  in
      FStar_Syntax_Syntax.mk uu____8281  in
    uu____8274 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8355 =
      let uu____8356 = unmeta t  in uu____8356.FStar_Syntax_Syntax.n  in
    match uu____8355 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____8360 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____8381 = is_t_true t1  in
      if uu____8381
      then t2
      else
        (let uu____8385 = is_t_true t2  in
         if uu____8385 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____8409 = is_t_true t1  in
      if uu____8409
      then t_true
      else
        (let uu____8413 = is_t_true t2  in
         if uu____8413 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____8437 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____8438 =
        let uu____8445 =
          let uu____8446 =
            let uu____8463 =
              let uu____8474 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____8483 =
                let uu____8494 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____8494]  in
              uu____8474 :: uu____8483  in
            (teq, uu____8463)  in
          FStar_Syntax_Syntax.Tm_app uu____8446  in
        FStar_Syntax_Syntax.mk uu____8445  in
      uu____8438 FStar_Pervasives_Native.None uu____8437
  
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
          let uu____8563 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____8564 =
            let uu____8571 =
              let uu____8572 =
                let uu____8589 =
                  let uu____8600 = FStar_Syntax_Syntax.iarg t  in
                  let uu____8609 =
                    let uu____8620 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____8629 =
                      let uu____8640 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____8640]  in
                    uu____8620 :: uu____8629  in
                  uu____8600 :: uu____8609  in
                (eq_inst, uu____8589)  in
              FStar_Syntax_Syntax.Tm_app uu____8572  in
            FStar_Syntax_Syntax.mk uu____8571  in
          uu____8564 FStar_Pervasives_Native.None uu____8563
  
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
        let uu____8719 =
          let uu____8726 =
            let uu____8727 =
              let uu____8744 =
                let uu____8755 = FStar_Syntax_Syntax.iarg t  in
                let uu____8764 =
                  let uu____8775 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____8784 =
                    let uu____8795 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____8795]  in
                  uu____8775 :: uu____8784  in
                uu____8755 :: uu____8764  in
              (t_has_type1, uu____8744)  in
            FStar_Syntax_Syntax.Tm_app uu____8727  in
          FStar_Syntax_Syntax.mk uu____8726  in
        uu____8719 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____8874 =
          let uu____8881 =
            let uu____8882 =
              let uu____8899 =
                let uu____8910 = FStar_Syntax_Syntax.iarg t  in
                let uu____8919 =
                  let uu____8930 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____8930]  in
                uu____8910 :: uu____8919  in
              (t_with_type1, uu____8899)  in
            FStar_Syntax_Syntax.Tm_app uu____8882  in
          FStar_Syntax_Syntax.mk uu____8881  in
        uu____8874 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____8978 =
    let uu____8985 =
      let uu____8986 =
        let uu____8993 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____8993, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____8986  in
    FStar_Syntax_Syntax.mk uu____8985  in
  uu____8978 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____9006 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____9019 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____9030 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____9006 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____9051  -> c0)
  
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
        let uu____9129 =
          let uu____9136 =
            let uu____9137 =
              let uu____9154 =
                let uu____9165 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____9174 =
                  let uu____9185 =
                    let uu____9194 =
                      let uu____9195 =
                        let uu____9196 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____9196]  in
                      abs uu____9195 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____9194  in
                  [uu____9185]  in
                uu____9165 :: uu____9174  in
              (fa, uu____9154)  in
            FStar_Syntax_Syntax.Tm_app uu____9137  in
          FStar_Syntax_Syntax.mk uu____9136  in
        uu____9129 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____9323 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____9323
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____9336 -> true
    | uu____9337 -> false
  
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
          let uu____9382 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____9382, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____9410 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____9410, FStar_Pervasives_Native.None, t2)  in
        let uu____9423 =
          let uu____9424 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____9424  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____9423
  
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
      let uu____9498 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____9501 =
        let uu____9512 = FStar_Syntax_Syntax.as_arg p  in [uu____9512]  in
      mk_app uu____9498 uu____9501
  
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
      let uu____9550 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____9553 =
        let uu____9564 = FStar_Syntax_Syntax.as_arg p  in [uu____9564]  in
      mk_app uu____9550 uu____9553
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____9598 = head_and_args t  in
    match uu____9598 with
    | (head1,args) ->
        let uu____9645 =
          let uu____9660 =
            let uu____9661 = un_uinst head1  in
            uu____9661.FStar_Syntax_Syntax.n  in
          (uu____9660, args)  in
        (match uu____9645 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____9680)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____9746 =
                    let uu____9751 =
                      let uu____9752 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____9752]  in
                    FStar_Syntax_Subst.open_term uu____9751 p  in
                  (match uu____9746 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____9809 -> failwith "impossible"  in
                       let uu____9816 =
                         let uu____9817 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____9817
                          in
                       if uu____9816
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____9831 -> FStar_Pervasives_Native.None)
         | uu____9834 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____9864 = head_and_args t  in
    match uu____9864 with
    | (head1,args) ->
        let uu____9915 =
          let uu____9930 =
            let uu____9931 = FStar_Syntax_Subst.compress head1  in
            uu____9931.FStar_Syntax_Syntax.n  in
          (uu____9930, args)  in
        (match uu____9915 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____9953;
               FStar_Syntax_Syntax.vars = uu____9954;_},u::[]),(t1,uu____9957)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10004 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10038 = head_and_args t  in
    match uu____10038 with
    | (head1,args) ->
        let uu____10089 =
          let uu____10104 =
            let uu____10105 = FStar_Syntax_Subst.compress head1  in
            uu____10105.FStar_Syntax_Syntax.n  in
          (uu____10104, args)  in
        (match uu____10089 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10127;
               FStar_Syntax_Syntax.vars = uu____10128;_},u::[]),(t1,uu____10131)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10178 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____10204 =
      let uu____10221 = unmeta t  in head_and_args uu____10221  in
    match uu____10204 with
    | (head1,uu____10223) ->
        let uu____10248 =
          let uu____10249 = un_uinst head1  in
          uu____10249.FStar_Syntax_Syntax.n  in
        (match uu____10248 with
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
         | uu____10253 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10271 =
      let uu____10284 =
        let uu____10285 = FStar_Syntax_Subst.compress t  in
        uu____10285.FStar_Syntax_Syntax.n  in
      match uu____10284 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____10414 =
            let uu____10425 =
              let uu____10426 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____10426  in
            (b, uu____10425)  in
          FStar_Pervasives_Native.Some uu____10414
      | uu____10443 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____10271
      (fun uu____10481  ->
         match uu____10481 with
         | (b,c) ->
             let uu____10518 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____10518 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____10581 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____10614 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____10614
  
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
    match projectee with | QAll _0 -> true | uu____10662 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____10700 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____10736 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____10773) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____10785) ->
          unmeta_monadic t
      | uu____10798 -> f2  in
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
      let aux f2 uu____10882 =
        match uu____10882 with
        | (lid,arity) ->
            let uu____10891 =
              let uu____10908 = unmeta_monadic f2  in
              head_and_args uu____10908  in
            (match uu____10891 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____10938 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____10938
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____11015 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____11015)
      | uu____11028 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____11089 = head_and_args t1  in
        match uu____11089 with
        | (t2,args) ->
            let uu____11144 = un_uinst t2  in
            let uu____11145 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____11186  ->
                      match uu____11186 with
                      | (t3,imp) ->
                          let uu____11205 = unascribe t3  in
                          (uu____11205, imp)))
               in
            (uu____11144, uu____11145)
         in
      let rec aux qopt out t1 =
        let uu____11254 = let uu____11277 = flat t1  in (qopt, uu____11277)
           in
        match uu____11254 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____11316;
                 FStar_Syntax_Syntax.vars = uu____11317;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____11320);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____11321;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____11322;_},uu____11323)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____11422;
                 FStar_Syntax_Syntax.vars = uu____11423;_},uu____11424::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____11427);
                  FStar_Syntax_Syntax.pos = uu____11428;
                  FStar_Syntax_Syntax.vars = uu____11429;_},uu____11430)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____11544;
               FStar_Syntax_Syntax.vars = uu____11545;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____11548);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____11549;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____11550;_},uu____11551)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____11642 =
              let uu____11645 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____11645  in
            aux uu____11642 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____11653;
               FStar_Syntax_Syntax.vars = uu____11654;_},uu____11655::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____11658);
                FStar_Syntax_Syntax.pos = uu____11659;
                FStar_Syntax_Syntax.vars = uu____11660;_},uu____11661)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____11768 =
              let uu____11771 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____11771  in
            aux uu____11768 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____11779) ->
            let bs = FStar_List.rev out  in
            let uu____11829 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____11829 with
             | (bs1,t2) ->
                 let uu____11838 = patterns t2  in
                 (match uu____11838 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____11886 -> FStar_Pervasives_Native.None  in
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
      let uu____11962 = un_squash t  in
      FStar_Util.bind_opt uu____11962
        (fun t1  ->
           let uu____11978 = head_and_args' t1  in
           match uu____11978 with
           | (hd1,args) ->
               let uu____12017 =
                 let uu____12022 =
                   let uu____12023 = un_uinst hd1  in
                   uu____12023.FStar_Syntax_Syntax.n  in
                 (uu____12022, (FStar_List.length args))  in
               (match uu____12017 with
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
                | uu____12044 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____12073 = un_squash t  in
      FStar_Util.bind_opt uu____12073
        (fun t1  ->
           let uu____12088 = arrow_one t1  in
           match uu____12088 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____12103 =
                 let uu____12104 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____12104  in
               if uu____12103
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____12111 = comp_to_comp_typ_nouniv c  in
                    uu____12111.FStar_Syntax_Syntax.result_typ  in
                  let uu____12112 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____12112
                  then
                    let uu____12117 = patterns q  in
                    match uu____12117 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____12179 =
                       let uu____12180 =
                         let uu____12185 =
                           let uu____12186 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____12197 =
                             let uu____12208 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____12208]  in
                           uu____12186 :: uu____12197  in
                         (FStar_Parser_Const.imp_lid, uu____12185)  in
                       BaseConn uu____12180  in
                     FStar_Pervasives_Native.Some uu____12179))
           | uu____12241 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____12249 = un_squash t  in
      FStar_Util.bind_opt uu____12249
        (fun t1  ->
           let uu____12280 = head_and_args' t1  in
           match uu____12280 with
           | (hd1,args) ->
               let uu____12319 =
                 let uu____12334 =
                   let uu____12335 = un_uinst hd1  in
                   uu____12335.FStar_Syntax_Syntax.n  in
                 (uu____12334, args)  in
               (match uu____12319 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____12352)::(a2,uu____12354)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____12405 =
                      let uu____12406 = FStar_Syntax_Subst.compress a2  in
                      uu____12406.FStar_Syntax_Syntax.n  in
                    (match uu____12405 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____12413) ->
                         let uu____12448 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____12448 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____12501 -> failwith "impossible"  in
                              let uu____12508 = patterns q1  in
                              (match uu____12508 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____12569 -> FStar_Pervasives_Native.None)
                | uu____12570 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____12593 = destruct_sq_forall phi  in
          (match uu____12593 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_11  -> FStar_Pervasives_Native.Some _0_11)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____12609 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____12615 = destruct_sq_exists phi  in
          (match uu____12615 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_12  -> FStar_Pervasives_Native.Some _0_12)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____12631 -> f1)
      | uu____12634 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____12638 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____12638
      (fun uu____12643  ->
         let uu____12644 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____12644
           (fun uu____12649  ->
              let uu____12650 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____12650
                (fun uu____12655  ->
                   let uu____12656 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____12656
                     (fun uu____12661  ->
                        let uu____12662 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____12662
                          (fun uu____12666  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____12678 =
      let uu____12679 = FStar_Syntax_Subst.compress t  in
      uu____12679.FStar_Syntax_Syntax.n  in
    match uu____12678 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____12686) ->
        let uu____12721 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____12721 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____12755 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____12755
             then
               let uu____12760 =
                 let uu____12771 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____12771]  in
               mk_app t uu____12760
             else e1)
    | uu____12797 ->
        let uu____12798 =
          let uu____12809 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____12809]  in
        mk_app t uu____12798
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____12850 =
            let uu____12855 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____12855  in
          let uu____12856 =
            let uu____12857 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____12857  in
          let uu____12860 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____12850 a.FStar_Syntax_Syntax.action_univs uu____12856
            FStar_Parser_Const.effect_Tot_lid uu____12860 [] pos
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
    let uu____12883 =
      let uu____12890 =
        let uu____12891 =
          let uu____12908 =
            let uu____12919 = FStar_Syntax_Syntax.as_arg t  in [uu____12919]
             in
          (reify_1, uu____12908)  in
        FStar_Syntax_Syntax.Tm_app uu____12891  in
      FStar_Syntax_Syntax.mk uu____12890  in
    uu____12883 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____12973 =
        let uu____12980 =
          let uu____12981 =
            let uu____12982 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____12982  in
          FStar_Syntax_Syntax.Tm_constant uu____12981  in
        FStar_Syntax_Syntax.mk uu____12980  in
      uu____12973 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____12986 =
      let uu____12993 =
        let uu____12994 =
          let uu____13011 =
            let uu____13022 = FStar_Syntax_Syntax.as_arg t  in [uu____13022]
             in
          (reflect_, uu____13011)  in
        FStar_Syntax_Syntax.Tm_app uu____12994  in
      FStar_Syntax_Syntax.mk uu____12993  in
    uu____12986 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13068 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____13092 = unfold_lazy i  in delta_qualifier uu____13092
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____13094 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____13095 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____13096 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____13119 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____13132 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____13133 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____13140 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____13141 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____13157) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____13162;
           FStar_Syntax_Syntax.index = uu____13163;
           FStar_Syntax_Syntax.sort = t2;_},uu____13165)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____13173) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____13179,uu____13180) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____13222) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____13247,t2,uu____13249) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____13274,t2) -> delta_qualifier t2
  
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
    let uu____13305 = delta_qualifier t  in incr_delta_depth uu____13305
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____13311 =
      let uu____13312 = FStar_Syntax_Subst.compress t  in
      uu____13312.FStar_Syntax_Syntax.n  in
    match uu____13311 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____13315 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____13329 =
      let uu____13346 = unmeta e  in head_and_args uu____13346  in
    match uu____13329 with
    | (head1,args) ->
        let uu____13377 =
          let uu____13392 =
            let uu____13393 = un_uinst head1  in
            uu____13393.FStar_Syntax_Syntax.n  in
          (uu____13392, args)  in
        (match uu____13377 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____13411) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____13435::(hd1,uu____13437)::(tl1,uu____13439)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____13506 =
               let uu____13509 =
                 let uu____13512 = list_elements tl1  in
                 FStar_Util.must uu____13512  in
               hd1 :: uu____13509  in
             FStar_Pervasives_Native.Some uu____13506
         | uu____13521 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____13544 .
    ('Auu____13544 -> 'Auu____13544) ->
      'Auu____13544 Prims.list -> 'Auu____13544 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____13569 = f a  in [uu____13569]
      | x::xs -> let uu____13574 = apply_last f xs  in x :: uu____13574
  
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
          let uu____13620 =
            let uu____13627 =
              let uu____13628 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____13628  in
            FStar_Syntax_Syntax.mk uu____13627  in
          uu____13620 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____13645 =
            let uu____13650 =
              let uu____13651 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____13651
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____13650 args  in
          uu____13645 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____13667 =
            let uu____13672 =
              let uu____13673 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____13673
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____13672 args  in
          uu____13667 FStar_Pervasives_Native.None pos  in
        let uu____13676 =
          let uu____13677 =
            let uu____13678 = FStar_Syntax_Syntax.iarg typ  in [uu____13678]
             in
          nil uu____13677 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____13712 =
                 let uu____13713 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____13722 =
                   let uu____13733 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____13742 =
                     let uu____13753 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____13753]  in
                   uu____13733 :: uu____13742  in
                 uu____13713 :: uu____13722  in
               cons1 uu____13712 t.FStar_Syntax_Syntax.pos) l uu____13676
  
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
        | uu____13857 -> false
  
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
          | uu____13964 -> false
  
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
        | uu____14119 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____14153 = FStar_ST.op_Bang debug_term_eq  in
          if uu____14153
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
        let t11 = let uu____14345 = unmeta_safe t1  in canon_app uu____14345
           in
        let t21 = let uu____14351 = unmeta_safe t2  in canon_app uu____14351
           in
        let uu____14354 =
          let uu____14359 =
            let uu____14360 =
              let uu____14363 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____14363  in
            uu____14360.FStar_Syntax_Syntax.n  in
          let uu____14364 =
            let uu____14365 =
              let uu____14368 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____14368  in
            uu____14365.FStar_Syntax_Syntax.n  in
          (uu____14359, uu____14364)  in
        match uu____14354 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____14369,uu____14370) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____14377,FStar_Syntax_Syntax.Tm_uinst uu____14378) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____14385,uu____14386) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____14409,FStar_Syntax_Syntax.Tm_delayed uu____14410) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____14433,uu____14434) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____14461,FStar_Syntax_Syntax.Tm_ascribed uu____14462) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____14495 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____14495
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____14498 = FStar_Const.eq_const c1 c2  in
            check "const" uu____14498
        | (FStar_Syntax_Syntax.Tm_type
           uu____14499,FStar_Syntax_Syntax.Tm_type uu____14500) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____14557 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____14557) &&
              (let uu____14565 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____14565)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____14612 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____14612) &&
              (let uu____14620 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____14620)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____14634 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____14634)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____14689 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____14689) &&
              (let uu____14691 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____14691)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____14778 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____14778) &&
              (let uu____14780 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____14780)
        | (FStar_Syntax_Syntax.Tm_lazy uu____14795,uu____14796) ->
            let uu____14797 =
              let uu____14798 = unlazy t11  in
              term_eq_dbg dbg uu____14798 t21  in
            check "lazy_l" uu____14797
        | (uu____14799,FStar_Syntax_Syntax.Tm_lazy uu____14800) ->
            let uu____14801 =
              let uu____14802 = unlazy t21  in
              term_eq_dbg dbg t11 uu____14802  in
            check "lazy_r" uu____14801
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____14838 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____14838))
              &&
              (let uu____14840 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____14840)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____14842),FStar_Syntax_Syntax.Tm_uvar (u2,uu____14844)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____14901 =
               let uu____14902 = eq_quoteinfo qi1 qi2  in uu____14902 = Equal
                in
             check "tm_quoted qi" uu____14901) &&
              (let uu____14904 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____14904)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____14931 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____14931) &&
                   (let uu____14933 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____14933)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____14950 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____14950) &&
                    (let uu____14952 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____14952))
                   &&
                   (let uu____14954 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____14954)
             | uu____14955 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____14960) -> fail "unk"
        | (uu____14961,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____14962,uu____14963) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____14964,uu____14965) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____14966,uu____14967) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____14968,uu____14969) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____14970,uu____14971) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____14972,uu____14973) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____14992,uu____14993) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15008,uu____15009) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15016,uu____15017) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15034,uu____15035) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____15058,uu____15059) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____15072,uu____15073) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____15086,uu____15087) ->
            fail "bottom"
        | (uu____15094,FStar_Syntax_Syntax.Tm_bvar uu____15095) ->
            fail "bottom"
        | (uu____15096,FStar_Syntax_Syntax.Tm_name uu____15097) ->
            fail "bottom"
        | (uu____15098,FStar_Syntax_Syntax.Tm_fvar uu____15099) ->
            fail "bottom"
        | (uu____15100,FStar_Syntax_Syntax.Tm_constant uu____15101) ->
            fail "bottom"
        | (uu____15102,FStar_Syntax_Syntax.Tm_type uu____15103) ->
            fail "bottom"
        | (uu____15104,FStar_Syntax_Syntax.Tm_abs uu____15105) ->
            fail "bottom"
        | (uu____15124,FStar_Syntax_Syntax.Tm_arrow uu____15125) ->
            fail "bottom"
        | (uu____15140,FStar_Syntax_Syntax.Tm_refine uu____15141) ->
            fail "bottom"
        | (uu____15148,FStar_Syntax_Syntax.Tm_app uu____15149) ->
            fail "bottom"
        | (uu____15166,FStar_Syntax_Syntax.Tm_match uu____15167) ->
            fail "bottom"
        | (uu____15190,FStar_Syntax_Syntax.Tm_let uu____15191) ->
            fail "bottom"
        | (uu____15204,FStar_Syntax_Syntax.Tm_uvar uu____15205) ->
            fail "bottom"
        | (uu____15218,FStar_Syntax_Syntax.Tm_meta uu____15219) ->
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
               let uu____15252 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____15252)
          (fun q1  ->
             fun q2  ->
               let uu____15262 =
                 let uu____15263 = eq_aqual q1 q2  in uu____15263 = Equal  in
               check "arg qual" uu____15262) a1 a2

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
               let uu____15286 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____15286)
          (fun q1  ->
             fun q2  ->
               let uu____15296 =
                 let uu____15297 = eq_aqual q1 q2  in uu____15297 = Equal  in
               check "binder qual" uu____15296) b1 b2

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
        ((let uu____15313 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____15313) &&
           (let uu____15315 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____15315))
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
    fun uu____15320  ->
      fun uu____15321  ->
        match (uu____15320, uu____15321) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____15446 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____15446) &&
               (let uu____15448 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____15448))
              &&
              (let uu____15450 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____15489 -> false  in
               check "branch when" uu____15450)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____15507 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____15507) &&
           (let uu____15513 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____15513))
          &&
          (let uu____15515 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____15515)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____15527 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____15527 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____15572 ->
        let uu____15595 =
          let uu____15596 = FStar_Syntax_Subst.compress t  in
          sizeof uu____15596  in
        (Prims.parse_int "1") + uu____15595
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____15598 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____15598
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____15600 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____15600
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____15607 = sizeof t1  in (FStar_List.length us) + uu____15607
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____15610) ->
        let uu____15635 = sizeof t1  in
        let uu____15636 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____15649  ->
                 match uu____15649 with
                 | (bv,uu____15657) ->
                     let uu____15662 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____15662) (Prims.parse_int "0") bs
           in
        uu____15635 + uu____15636
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____15689 = sizeof hd1  in
        let uu____15690 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____15703  ->
                 match uu____15703 with
                 | (arg,uu____15711) ->
                     let uu____15716 = sizeof arg  in acc + uu____15716)
            (Prims.parse_int "0") args
           in
        uu____15689 + uu____15690
    | uu____15717 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____15728 =
        let uu____15729 = un_uinst t  in uu____15729.FStar_Syntax_Syntax.n
         in
      match uu____15728 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____15733 -> false
  
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
        let uu____15774 = FStar_Options.set_options t s  in
        match uu____15774 with
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
          ((let uu____15782 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____15782 (fun a1  -> ()));
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
          let uu____15789 = FStar_Options.internal_pop ()  in
          if uu____15789
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
    | FStar_Syntax_Syntax.Tm_delayed uu____15815 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____15841 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____15856 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____15857 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____15858 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____15867) ->
        let uu____15892 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____15892 with
         | (bs1,t2) ->
             let uu____15901 =
               FStar_List.collect
                 (fun uu____15913  ->
                    match uu____15913 with
                    | (b,uu____15923) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____15928 = unbound_variables t2  in
             FStar_List.append uu____15901 uu____15928)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____15953 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____15953 with
         | (bs1,c1) ->
             let uu____15962 =
               FStar_List.collect
                 (fun uu____15974  ->
                    match uu____15974 with
                    | (b,uu____15984) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____15989 = unbound_variables_comp c1  in
             FStar_List.append uu____15962 uu____15989)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____15998 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____15998 with
         | (bs,t2) ->
             let uu____16021 =
               FStar_List.collect
                 (fun uu____16033  ->
                    match uu____16033 with
                    | (b1,uu____16043) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____16048 = unbound_variables t2  in
             FStar_List.append uu____16021 uu____16048)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____16077 =
          FStar_List.collect
            (fun uu____16091  ->
               match uu____16091 with
               | (x,uu____16103) -> unbound_variables x) args
           in
        let uu____16112 = unbound_variables t1  in
        FStar_List.append uu____16077 uu____16112
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____16153 = unbound_variables t1  in
        let uu____16156 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____16171 = FStar_Syntax_Subst.open_branch br  in
                  match uu____16171 with
                  | (p,wopt,t2) ->
                      let uu____16193 = unbound_variables t2  in
                      let uu____16196 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____16193 uu____16196))
           in
        FStar_List.append uu____16153 uu____16156
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____16210) ->
        let uu____16251 = unbound_variables t1  in
        let uu____16254 =
          let uu____16257 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____16288 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____16257 uu____16288  in
        FStar_List.append uu____16251 uu____16254
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____16326 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____16329 =
          let uu____16332 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____16335 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____16340 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____16342 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____16342 with
                 | (uu____16363,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____16332 uu____16335  in
        FStar_List.append uu____16326 uu____16329
    | FStar_Syntax_Syntax.Tm_let ((uu____16365,lbs),t1) ->
        let uu____16382 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____16382 with
         | (lbs1,t2) ->
             let uu____16397 = unbound_variables t2  in
             let uu____16400 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____16407 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____16410 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____16407 uu____16410) lbs1
                in
             FStar_List.append uu____16397 uu____16400)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____16427 = unbound_variables t1  in
        let uu____16430 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____16469  ->
                      match uu____16469 with
                      | (a,uu____16481) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____16490,uu____16491,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____16497,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____16503 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____16510 -> []
          | FStar_Syntax_Syntax.Meta_named uu____16511 -> []  in
        FStar_List.append uu____16427 uu____16430

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____16518) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____16528) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____16538 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____16541 =
          FStar_List.collect
            (fun uu____16555  ->
               match uu____16555 with
               | (a,uu____16567) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____16538 uu____16541

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
            let uu____16681 = head_and_args h  in
            (match uu____16681 with
             | (head1,args) ->
                 let uu____16742 =
                   let uu____16743 = FStar_Syntax_Subst.compress head1  in
                   uu____16743.FStar_Syntax_Syntax.n  in
                 (match uu____16742 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____16796 -> aux (h :: acc) t))
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
      let uu____16819 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____16819 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___133_16861 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___133_16861.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___133_16861.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___133_16861.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___133_16861.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  