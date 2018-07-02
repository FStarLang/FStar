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
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____170 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____170
            then []
            else (let uu____182 = arg_of_non_null_binder b  in [uu____182])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  =
  fun binders  ->
    let uu____208 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____272 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____272
              then
                let b1 =
                  let uu____290 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____290, (FStar_Pervasives_Native.snd b))  in
                let uu____291 = arg_of_non_null_binder b1  in (b1, uu____291)
              else
                (let uu____305 = arg_of_non_null_binder b  in (b, uu____305))))
       in
    FStar_All.pipe_right uu____208 FStar_List.unzip
  
let (name_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____405 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____405
              then
                let uu____410 = b  in
                match uu____410 with
                | (a,imp) ->
                    let b1 =
                      let uu____422 =
                        let uu____423 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____423  in
                      FStar_Ident.id_of_text uu____422  in
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
        let uu____457 =
          let uu____464 =
            let uu____465 =
              let uu____478 = name_binders binders  in (uu____478, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____465  in
          FStar_Syntax_Syntax.mk uu____464  in
        uu____457 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____496 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____532  ->
            match uu____532 with
            | (t,imp) ->
                let uu____543 =
                  let uu____544 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____544
                   in
                (uu____543, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____592  ->
            match uu____592 with
            | (t,imp) ->
                let uu____609 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____609, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____621 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____621
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____632 . 'Auu____632 -> 'Auu____632 Prims.list =
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
          (fun uu____728  ->
             fun uu____729  ->
               match (uu____728, uu____729) with
               | ((x,uu____747),(y,uu____749)) ->
                   let uu____758 =
                     let uu____765 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____765)  in
                   FStar_Syntax_Syntax.NT uu____758) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____778) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____784,uu____785) -> unmeta e2
    | uu____826 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____839 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____846 -> e1
         | uu____855 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____857,uu____858) ->
        unmeta_safe e2
    | uu____899 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____913 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____914 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____924 = univ_kernel u1  in
        (match uu____924 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____935 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____942 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____952 = univ_kernel u  in FStar_Pervasives_Native.snd uu____952
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____967,uu____968) ->
          failwith "Impossible: compare_univs"
      | (uu____969,FStar_Syntax_Syntax.U_bvar uu____970) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____971) ->
          ~- (Prims.parse_int "1")
      | (uu____972,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____973) -> ~- (Prims.parse_int "1")
      | (uu____974,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____977,FStar_Syntax_Syntax.U_unif
         uu____978) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____987,FStar_Syntax_Syntax.U_name
         uu____988) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____1015 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____1016 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____1015 - uu____1016
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____1047 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____1047
                 (fun uu____1062  ->
                    match uu____1062 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1076,uu____1077) ->
          ~- (Prims.parse_int "1")
      | (uu____1080,FStar_Syntax_Syntax.U_max uu____1081) ->
          (Prims.parse_int "1")
      | uu____1084 ->
          let uu____1089 = univ_kernel u1  in
          (match uu____1089 with
           | (k1,n1) ->
               let uu____1096 = univ_kernel u2  in
               (match uu____1096 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1115 = compare_univs u1 u2  in
      uu____1115 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1130 =
        let uu____1131 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1131;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1130
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1148 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1157 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1179 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1188 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1214 =
          let uu____1215 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1215  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1214;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1242 =
          let uu____1243 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1243  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1242;
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
      let uu___116_1276 = c  in
      let uu____1277 =
        let uu____1278 =
          let uu___117_1279 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___117_1279.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___117_1279.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___117_1279.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___117_1279.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1278  in
      {
        FStar_Syntax_Syntax.n = uu____1277;
        FStar_Syntax_Syntax.pos = (uu___116_1276.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___116_1276.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1304 -> c
        | FStar_Syntax_Syntax.GTotal uu____1313 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___118_1324 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___118_1324.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___118_1324.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___118_1324.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___118_1324.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___119_1325 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___119_1325.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___119_1325.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1328  ->
           let uu____1329 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1329)
  
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
    | uu____1364 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1375 -> true
    | FStar_Syntax_Syntax.GTotal uu____1384 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___104_1405  ->
               match uu___104_1405 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1406 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___105_1415  ->
               match uu___105_1415 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1416 -> false)))
  
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
            (fun uu___106_1425  ->
               match uu___106_1425 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1426 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___107_1439  ->
            match uu___107_1439 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1440 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___108_1449  ->
            match uu___108_1449 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1450 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1474 -> true
    | FStar_Syntax_Syntax.GTotal uu____1483 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___109_1496  ->
                   match uu___109_1496 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1497 -> false)))
  
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
            (fun uu___110_1530  ->
               match uu___110_1530 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1531 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1542 =
      let uu____1543 = FStar_Syntax_Subst.compress t  in
      uu____1543.FStar_Syntax_Syntax.n  in
    match uu____1542 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1546,c) -> is_pure_or_ghost_comp c
    | uu____1564 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1575 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1581 =
      let uu____1582 = FStar_Syntax_Subst.compress t  in
      uu____1582.FStar_Syntax_Syntax.n  in
    match uu____1581 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1585,c) -> is_lemma_comp c
    | uu____1603 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1609 =
      let uu____1610 = FStar_Syntax_Subst.compress t  in
      uu____1610.FStar_Syntax_Syntax.n  in
    match uu____1609 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1614) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____1636) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____1673,t1,uu____1675) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1697,uu____1698) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1740) -> head_of t1
    | uu____1745 -> t
  
let (head_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax,
                                                            FStar_Syntax_Syntax.aqual)
                                                            FStar_Pervasives_Native.tuple2
                                                            Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____1812 -> (t1, [])
  
let rec (head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.term'
                                 FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1881 = head_and_args' head1  in
        (match uu____1881 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1938 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1960) ->
        FStar_Syntax_Subst.compress t2
    | uu____1965 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1971 =
      let uu____1972 = FStar_Syntax_Subst.compress t  in
      uu____1972.FStar_Syntax_Syntax.n  in
    match uu____1971 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1975,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1997)::uu____1998 ->
                  let pats' = unmeta pats  in
                  let uu____2042 = head_and_args pats'  in
                  (match uu____2042 with
                   | (head1,uu____2058) ->
                       let uu____2079 =
                         let uu____2080 = un_uinst head1  in
                         uu____2080.FStar_Syntax_Syntax.n  in
                       (match uu____2079 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____2084 -> false))
              | uu____2085 -> false)
         | uu____2094 -> false)
    | uu____2095 -> false
  
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
                (fun uu___111_2109  ->
                   match uu___111_2109 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2110 -> false)))
    | uu____2111 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2126) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2136) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2164 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2173 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___120_2185 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___120_2185.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___120_2185.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___120_2185.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___120_2185.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2198  ->
           let uu____2199 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____2199 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___112_2214  ->
            match uu___112_2214 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2215 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2221 -> []
    | FStar_Syntax_Syntax.GTotal uu____2236 -> []
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
    | uu____2271 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2279,uu____2280) ->
        unascribe e2
    | uu____2321 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2373,uu____2374) ->
          ascribe t' k
      | uu____2415 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2441 =
      let uu____2450 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2450  in
    uu____2441 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2505 =
      let uu____2506 = FStar_Syntax_Subst.compress t  in
      uu____2506.FStar_Syntax_Syntax.n  in
    match uu____2505 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2510 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2510
    | uu____2511 -> t
  
let rec unlazy_as_t :
  'Auu____2518 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2518
  =
  fun k  ->
    fun t  ->
      let uu____2529 =
        let uu____2530 = FStar_Syntax_Subst.compress t  in
        uu____2530.FStar_Syntax_Syntax.n  in
      match uu____2529 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.typ = uu____2535;
            FStar_Syntax_Syntax.rng = uu____2536;_}
          when k = k' -> FStar_Dyn.undyn v1
      | uu____2539 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2578 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2578;
              FStar_Syntax_Syntax.lkind = k;
              FStar_Syntax_Syntax.typ = typ;
              FStar_Syntax_Syntax.rng = rng
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i)
            FStar_Pervasives_Native.None rng
  
let (canon_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____2590 =
      let uu____2603 = unascribe t  in head_and_args' uu____2603  in
    match uu____2590 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2629 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2635 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2641 -> false
  
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
      let equal_if uu___113_2717 = if uu___113_2717 then Equal else Unknown
         in
      let equal_iff uu___114_2724 = if uu___114_2724 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2742 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2754) -> NotEqual
        | (uu____2755,NotEqual ) -> NotEqual
        | (Unknown ,uu____2756) -> Unknown
        | (uu____2757,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____2803 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2803
        then
          let uu____2805 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2863  ->
                    match uu____2863 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2889 = eq_tm a1 a2  in
                        eq_inj acc uu____2889) Equal) uu____2805
        else NotEqual  in
      let uu____2891 =
        let uu____2896 =
          let uu____2897 = unmeta t11  in uu____2897.FStar_Syntax_Syntax.n
           in
        let uu____2900 =
          let uu____2901 = unmeta t21  in uu____2901.FStar_Syntax_Syntax.n
           in
        (uu____2896, uu____2900)  in
      match uu____2891 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2906,uu____2907) ->
          let uu____2908 = unlazy t11  in eq_tm uu____2908 t21
      | (uu____2909,FStar_Syntax_Syntax.Tm_lazy uu____2910) ->
          let uu____2911 = unlazy t21  in eq_tm t11 uu____2911
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
            (let uu____2929 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2929)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2942 = eq_tm f g  in
          eq_and uu____2942
            (fun uu____2945  ->
               let uu____2946 = eq_univs_list us vs  in equal_if uu____2946)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2947),uu____2948) -> Unknown
      | (uu____2949,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2950)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2953 = FStar_Const.eq_const c d  in equal_iff uu____2953
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____2955)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____2957))) ->
          let uu____2986 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____2986
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3031 =
            let uu____3036 =
              let uu____3037 = un_uinst h1  in
              uu____3037.FStar_Syntax_Syntax.n  in
            let uu____3040 =
              let uu____3041 = un_uinst h2  in
              uu____3041.FStar_Syntax_Syntax.n  in
            (uu____3036, uu____3040)  in
          (match uu____3031 with
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
                 (let uu____3053 =
                    let uu____3054 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3054  in
                  FStar_List.mem uu____3053 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3055 ->
               let uu____3060 = eq_tm h1 h2  in
               eq_and uu____3060 (fun uu____3062  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3167 = FStar_List.zip bs1 bs2  in
            let uu____3230 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3267  ->
                 fun a  ->
                   match uu____3267 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3360  -> branch_matches b1 b2))
              uu____3167 uu____3230
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3364 = eq_univs u v1  in equal_if uu____3364
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) -> if q1 = q2 then eq_tm t12 t22 else Unknown
      | uu____3378 -> Unknown

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
        | (uu____3461,uu____3462) -> false  in
      let uu____3471 = b1  in
      match uu____3471 with
      | (p1,w1,t1) ->
          let uu____3505 = b2  in
          (match uu____3505 with
           | (p2,w2,t2) ->
               let uu____3539 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3539
               then
                 let uu____3540 =
                   (let uu____3543 = eq_tm t1 t2  in uu____3543 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3552 = eq_tm t11 t21  in
                             uu____3552 = Equal) w1 w2)
                    in
                 (if uu____3540 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3602)::a11,(b,uu____3605)::b1) ->
          let uu____3659 = eq_tm a b  in
          (match uu____3659 with
           | Equal  -> eq_args a11 b1
           | uu____3660 -> Unknown)
      | uu____3661 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3691) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3697,uu____3698) ->
        unrefine t2
    | uu____3739 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3745 =
      let uu____3746 = FStar_Syntax_Subst.compress t  in
      uu____3746.FStar_Syntax_Syntax.n  in
    match uu____3745 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3749 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3763) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____3768 ->
        let uu____3783 =
          let uu____3784 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____3784 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____3783 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3838,uu____3839) ->
        is_uvar t1
    | uu____3880 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3886 =
      let uu____3887 = unrefine t  in uu____3887.FStar_Syntax_Syntax.n  in
    match uu____3886 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3892) -> is_unit t1
    | uu____3897 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3903 =
      let uu____3904 = unrefine t  in uu____3904.FStar_Syntax_Syntax.n  in
    match uu____3903 with
    | FStar_Syntax_Syntax.Tm_type uu____3907 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3910) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3932) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3937,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3955 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____3961 =
      let uu____3962 = FStar_Syntax_Subst.compress e  in
      uu____3962.FStar_Syntax_Syntax.n  in
    match uu____3961 with
    | FStar_Syntax_Syntax.Tm_abs uu____3965 -> true
    | uu____3982 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3988 =
      let uu____3989 = FStar_Syntax_Subst.compress t  in
      uu____3989.FStar_Syntax_Syntax.n  in
    match uu____3988 with
    | FStar_Syntax_Syntax.Tm_arrow uu____3992 -> true
    | uu____4005 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4013) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4019,uu____4020) ->
        pre_typ t2
    | uu____4061 -> t1
  
let (destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ  in
      let uu____4083 =
        let uu____4084 = un_uinst typ1  in uu____4084.FStar_Syntax_Syntax.n
         in
      match uu____4083 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____4139 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____4163 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____4181,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____4188) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____4193,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____4204,uu____4205,uu____4206,uu____4207,uu____4208) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____4218,uu____4219,uu____4220,uu____4221) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____4227,uu____4228,uu____4229,uu____4230,uu____4231) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____4237,uu____4238) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4240,uu____4241) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____4244 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____4245 -> []
    | FStar_Syntax_Syntax.Sig_main uu____4246 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____4259 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___115_4282  ->
    match uu___115_4282 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____4295 'Auu____4296 .
    ('Auu____4295 FStar_Syntax_Syntax.syntax,'Auu____4296)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____4307  ->
    match uu____4307 with | (hd1,uu____4315) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____4328 'Auu____4329 .
    ('Auu____4328 FStar_Syntax_Syntax.syntax,'Auu____4329)
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
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____4420 ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args))
            FStar_Pervasives_Native.None r
  
let (mk_data :
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Syntax_Syntax.syntax)
  =
  fun l  ->
    fun args  ->
      match args with
      | [] ->
          let uu____4480 = FStar_Ident.range_of_lid l  in
          let uu____4481 =
            let uu____4490 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____4490  in
          uu____4481 FStar_Pervasives_Native.None uu____4480
      | uu____4498 ->
          let e =
            let uu____4510 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____4510 args  in
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
      let uu____4525 =
        let uu____4530 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____4530, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____4525
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
          let uu____4581 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____4581
          then
            let uu____4582 =
              let uu____4587 =
                let uu____4588 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____4588  in
              let uu____4589 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____4587, uu____4589)  in
            FStar_Ident.mk_ident uu____4582
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___121_4592 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___121_4592.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___121_4592.FStar_Syntax_Syntax.sort)
          }  in
        let uu____4593 = mk_field_projector_name_from_ident lid nm  in
        (uu____4593, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4604) -> ses
    | uu____4613 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____4622 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____4633 = FStar_Syntax_Unionfind.find uv  in
      match uu____4633 with
      | FStar_Pervasives_Native.Some uu____4636 ->
          let uu____4637 =
            let uu____4638 =
              let uu____4639 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____4639  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4638  in
          failwith uu____4637
      | uu____4640 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____4715 -> q1 = q2
  
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
              let uu____4760 =
                let uu___122_4761 = rc  in
                let uu____4762 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___122_4761.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____4762;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___122_4761.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____4760
           in
        match bs with
        | [] -> t
        | uu____4777 ->
            let body =
              let uu____4779 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4779  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4809 =
                   let uu____4816 =
                     let uu____4817 =
                       let uu____4834 =
                         let uu____4841 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4841 bs'  in
                       let uu____4852 = close_lopt lopt'  in
                       (uu____4834, t1, uu____4852)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4817  in
                   FStar_Syntax_Syntax.mk uu____4816  in
                 uu____4809 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4868 ->
                 let uu____4875 =
                   let uu____4882 =
                     let uu____4883 =
                       let uu____4900 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4907 = close_lopt lopt  in
                       (uu____4900, body, uu____4907)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4883  in
                   FStar_Syntax_Syntax.mk uu____4882  in
                 uu____4875 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos)
  
let (arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____4957 ->
          let uu____4964 =
            let uu____4971 =
              let uu____4972 =
                let uu____4985 = FStar_Syntax_Subst.close_binders bs  in
                let uu____4992 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____4985, uu____4992)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4972  in
            FStar_Syntax_Syntax.mk uu____4971  in
          uu____4964 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____5037 =
        let uu____5038 = FStar_Syntax_Subst.compress t  in
        uu____5038.FStar_Syntax_Syntax.n  in
      match uu____5037 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____5064) ->
               let uu____5073 =
                 let uu____5074 = FStar_Syntax_Subst.compress tres  in
                 uu____5074.FStar_Syntax_Syntax.n  in
               (match uu____5073 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____5109 -> t)
           | uu____5110 -> t)
      | uu____5111 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____5128 =
        let uu____5129 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____5129 t.FStar_Syntax_Syntax.pos  in
      let uu____5130 =
        let uu____5137 =
          let uu____5138 =
            let uu____5145 =
              let uu____5148 =
                let uu____5149 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____5149]  in
              FStar_Syntax_Subst.close uu____5148 t  in
            (b, uu____5145)  in
          FStar_Syntax_Syntax.Tm_refine uu____5138  in
        FStar_Syntax_Syntax.mk uu____5137  in
      uu____5130 FStar_Pervasives_Native.None uu____5128
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____5216 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____5216 with
         | (bs1,c1) ->
             let uu____5233 = is_total_comp c1  in
             if uu____5233
             then
               let uu____5244 = arrow_formals_comp (comp_result c1)  in
               (match uu____5244 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____5296;
           FStar_Syntax_Syntax.index = uu____5297;
           FStar_Syntax_Syntax.sort = k2;_},uu____5299)
        -> arrow_formals_comp k2
    | uu____5306 ->
        let uu____5307 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____5307)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____5335 = arrow_formals_comp k  in
    match uu____5335 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____5417 =
            let uu___123_5418 = rc  in
            let uu____5419 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___123_5418.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____5419;
              FStar_Syntax_Syntax.residual_flags =
                (uu___123_5418.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____5417
      | uu____5428 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____5460 =
        let uu____5461 =
          let uu____5464 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____5464  in
        uu____5461.FStar_Syntax_Syntax.n  in
      match uu____5460 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____5504 = aux t2 what  in
          (match uu____5504 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____5564 -> ([], t1, abs_body_lcomp)  in
    let uu____5577 = aux t FStar_Pervasives_Native.None  in
    match uu____5577 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____5619 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____5619 with
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
                    | (FStar_Pervasives_Native.None ,uu____5780) -> def
                    | (uu____5791,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____5803) ->
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
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                          FStar_Pervasives_Native.tuple2
                                          Prims.list,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple3)
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____5889 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____5889 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5918 ->
            let t' = arrow binders c  in
            let uu____5928 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5928 with
             | (uvs1,t'1) ->
                 let uu____5947 =
                   let uu____5948 = FStar_Syntax_Subst.compress t'1  in
                   uu____5948.FStar_Syntax_Syntax.n  in
                 (match uu____5947 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____5989 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____6008 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____6015 -> false
  
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
      let uu____6063 =
        let uu____6064 = pre_typ t  in uu____6064.FStar_Syntax_Syntax.n  in
      match uu____6063 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____6068 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____6079 =
        let uu____6080 = pre_typ t  in uu____6080.FStar_Syntax_Syntax.n  in
      match uu____6079 with
      | FStar_Syntax_Syntax.Tm_fvar uu____6083 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____6085) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6107) ->
          is_constructed_typ t1 lid
      | uu____6112 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____6123 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____6124 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____6125 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____6127) -> get_tycon t2
    | uu____6148 -> FStar_Pervasives_Native.None
  
let (is_interpreted : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    let theory_syms =
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
      FStar_Parser_Const.op_Negation]  in
    FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____6162 =
      let uu____6163 = un_uinst t  in uu____6163.FStar_Syntax_Syntax.n  in
    match uu____6162 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____6167 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____6174 =
        let uu____6177 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____6177  in
      match uu____6174 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____6190 -> false
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
  fun uu____6202  ->
    let u =
      let uu____6208 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_5  -> FStar_Syntax_Syntax.U_unif _0_5)
        uu____6208
       in
    let uu____6225 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____6225, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____6236 = eq_tm a a'  in
      match uu____6236 with | Equal  -> true | uu____6237 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____6240 =
    let uu____6247 =
      let uu____6248 =
        let uu____6249 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____6249
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____6248  in
    FStar_Syntax_Syntax.mk uu____6247  in
  uu____6240 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____6324 =
            let uu____6327 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____6328 =
              let uu____6335 =
                let uu____6336 =
                  let uu____6351 =
                    let uu____6360 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____6367 =
                      let uu____6376 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____6376]  in
                    uu____6360 :: uu____6367  in
                  (tand, uu____6351)  in
                FStar_Syntax_Syntax.Tm_app uu____6336  in
              FStar_Syntax_Syntax.mk uu____6335  in
            uu____6328 FStar_Pervasives_Native.None uu____6327  in
          FStar_Pervasives_Native.Some uu____6324
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____6445 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____6446 =
          let uu____6453 =
            let uu____6454 =
              let uu____6469 =
                let uu____6478 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____6485 =
                  let uu____6494 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____6494]  in
                uu____6478 :: uu____6485  in
              (op_t, uu____6469)  in
            FStar_Syntax_Syntax.Tm_app uu____6454  in
          FStar_Syntax_Syntax.mk uu____6453  in
        uu____6446 FStar_Pervasives_Native.None uu____6445
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____6543 =
      let uu____6550 =
        let uu____6551 =
          let uu____6566 =
            let uu____6575 = FStar_Syntax_Syntax.as_arg phi  in [uu____6575]
             in
          (t_not, uu____6566)  in
        FStar_Syntax_Syntax.Tm_app uu____6551  in
      FStar_Syntax_Syntax.mk uu____6550  in
    uu____6543 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____6760 =
      let uu____6767 =
        let uu____6768 =
          let uu____6783 =
            let uu____6792 = FStar_Syntax_Syntax.as_arg e  in [uu____6792]
             in
          (b2t_v, uu____6783)  in
        FStar_Syntax_Syntax.Tm_app uu____6768  in
      FStar_Syntax_Syntax.mk uu____6767  in
    uu____6760 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____6829 =
      let uu____6830 = unmeta t  in uu____6830.FStar_Syntax_Syntax.n  in
    match uu____6829 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____6834 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____6855 = is_t_true t1  in
      if uu____6855
      then t2
      else
        (let uu____6859 = is_t_true t2  in
         if uu____6859 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____6883 = is_t_true t1  in
      if uu____6883
      then t_true
      else
        (let uu____6887 = is_t_true t2  in
         if uu____6887 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____6911 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____6912 =
        let uu____6919 =
          let uu____6920 =
            let uu____6935 =
              let uu____6944 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____6951 =
                let uu____6960 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____6960]  in
              uu____6944 :: uu____6951  in
            (teq, uu____6935)  in
          FStar_Syntax_Syntax.Tm_app uu____6920  in
        FStar_Syntax_Syntax.mk uu____6919  in
      uu____6912 FStar_Pervasives_Native.None uu____6911
  
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
          let uu____7019 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____7020 =
            let uu____7027 =
              let uu____7028 =
                let uu____7043 =
                  let uu____7052 = FStar_Syntax_Syntax.iarg t  in
                  let uu____7059 =
                    let uu____7068 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____7075 =
                      let uu____7084 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____7084]  in
                    uu____7068 :: uu____7075  in
                  uu____7052 :: uu____7059  in
                (eq_inst, uu____7043)  in
              FStar_Syntax_Syntax.Tm_app uu____7028  in
            FStar_Syntax_Syntax.mk uu____7027  in
          uu____7020 FStar_Pervasives_Native.None uu____7019
  
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
        let uu____7151 =
          let uu____7158 =
            let uu____7159 =
              let uu____7174 =
                let uu____7183 = FStar_Syntax_Syntax.iarg t  in
                let uu____7190 =
                  let uu____7199 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____7206 =
                    let uu____7215 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____7215]  in
                  uu____7199 :: uu____7206  in
                uu____7183 :: uu____7190  in
              (t_has_type1, uu____7174)  in
            FStar_Syntax_Syntax.Tm_app uu____7159  in
          FStar_Syntax_Syntax.mk uu____7158  in
        uu____7151 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____7282 =
          let uu____7289 =
            let uu____7290 =
              let uu____7305 =
                let uu____7314 = FStar_Syntax_Syntax.iarg t  in
                let uu____7321 =
                  let uu____7330 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____7330]  in
                uu____7314 :: uu____7321  in
              (t_with_type1, uu____7305)  in
            FStar_Syntax_Syntax.Tm_app uu____7290  in
          FStar_Syntax_Syntax.mk uu____7289  in
        uu____7282 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____7368 =
    let uu____7375 =
      let uu____7376 =
        let uu____7383 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____7383, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____7376  in
    FStar_Syntax_Syntax.mk uu____7375  in
  uu____7368 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____7396 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____7409 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____7420 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____7396 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____7441  -> c0)
  
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
        let uu____7519 =
          let uu____7526 =
            let uu____7527 =
              let uu____7542 =
                let uu____7551 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____7558 =
                  let uu____7567 =
                    let uu____7574 =
                      let uu____7575 =
                        let uu____7576 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____7576]  in
                      abs uu____7575 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____7574  in
                  [uu____7567]  in
                uu____7551 :: uu____7558  in
              (fa, uu____7542)  in
            FStar_Syntax_Syntax.Tm_app uu____7527  in
          FStar_Syntax_Syntax.mk uu____7526  in
        uu____7519 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____7681 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____7681
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____7692 -> true
    | uu____7693 -> false
  
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
          let uu____7738 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____7738, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____7766 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____7766, FStar_Pervasives_Native.None, t2)  in
        let uu____7779 =
          let uu____7780 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____7780  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____7779
  
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
      let uu____7854 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7857 =
        let uu____7866 = FStar_Syntax_Syntax.as_arg p  in [uu____7866]  in
      mk_app uu____7854 uu____7857
  
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
      let uu____7898 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7901 =
        let uu____7910 = FStar_Syntax_Syntax.as_arg p  in [uu____7910]  in
      mk_app uu____7898 uu____7901
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7938 = head_and_args t  in
    match uu____7938 with
    | (head1,args) ->
        let uu____7979 =
          let uu____7992 =
            let uu____7993 = un_uinst head1  in
            uu____7993.FStar_Syntax_Syntax.n  in
          (uu____7992, args)  in
        (match uu____7979 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____8010)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____8062 =
                    let uu____8067 =
                      let uu____8068 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____8068]  in
                    FStar_Syntax_Subst.open_term uu____8067 p  in
                  (match uu____8062 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____8109 -> failwith "impossible"  in
                       let uu____8114 =
                         let uu____8115 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____8115
                          in
                       if uu____8114
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____8127 -> FStar_Pervasives_Native.None)
         | uu____8130 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8158 = head_and_args t  in
    match uu____8158 with
    | (head1,args) ->
        let uu____8203 =
          let uu____8216 =
            let uu____8217 = FStar_Syntax_Subst.compress head1  in
            uu____8217.FStar_Syntax_Syntax.n  in
          (uu____8216, args)  in
        (match uu____8203 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____8237;
               FStar_Syntax_Syntax.vars = uu____8238;_},u::[]),(t1,uu____8241)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____8278 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8310 = head_and_args t  in
    match uu____8310 with
    | (head1,args) ->
        let uu____8355 =
          let uu____8368 =
            let uu____8369 = FStar_Syntax_Subst.compress head1  in
            uu____8369.FStar_Syntax_Syntax.n  in
          (uu____8368, args)  in
        (match uu____8355 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____8389;
               FStar_Syntax_Syntax.vars = uu____8390;_},u::[]),(t1,uu____8393)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____8430 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8454 = let uu____8469 = unmeta t  in head_and_args uu____8469
       in
    match uu____8454 with
    | (head1,uu____8471) ->
        let uu____8492 =
          let uu____8493 = un_uinst head1  in
          uu____8493.FStar_Syntax_Syntax.n  in
        (match uu____8492 with
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
         | uu____8497 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8515 =
      let uu____8526 =
        let uu____8527 = FStar_Syntax_Subst.compress t  in
        uu____8527.FStar_Syntax_Syntax.n  in
      match uu____8526 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____8628 =
            let uu____8637 =
              let uu____8638 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____8638  in
            (b, uu____8637)  in
          FStar_Pervasives_Native.Some uu____8628
      | uu____8651 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____8515
      (fun uu____8683  ->
         match uu____8683 with
         | (b,c) ->
             let uu____8712 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____8712 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____8759 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____8786 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8786
  
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
    match projectee with | QAll _0 -> true | uu____8834 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____8872 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____8908 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____8945) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____8957) ->
          unmeta_monadic t
      | uu____8970 -> f2  in
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
      let aux f2 uu____9054 =
        match uu____9054 with
        | (lid,arity) ->
            let uu____9063 =
              let uu____9078 = unmeta_monadic f2  in head_and_args uu____9078
               in
            (match uu____9063 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____9104 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____9104
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____9173 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____9173)
      | uu____9184 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____9239 = head_and_args t1  in
        match uu____9239 with
        | (t2,args) ->
            let uu____9286 = un_uinst t2  in
            let uu____9287 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9318  ->
                      match uu____9318 with
                      | (t3,imp) ->
                          let uu____9329 = unascribe t3  in (uu____9329, imp)))
               in
            (uu____9286, uu____9287)
         in
      let rec aux qopt out t1 =
        let uu____9370 = let uu____9391 = flat t1  in (qopt, uu____9391)  in
        match uu____9370 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____9426;
                 FStar_Syntax_Syntax.vars = uu____9427;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____9430);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____9431;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____9432;_},uu____9433)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____9510;
                 FStar_Syntax_Syntax.vars = uu____9511;_},uu____9512::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____9515);
                  FStar_Syntax_Syntax.pos = uu____9516;
                  FStar_Syntax_Syntax.vars = uu____9517;_},uu____9518)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9606;
               FStar_Syntax_Syntax.vars = uu____9607;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____9610);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____9611;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____9612;_},uu____9613)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9684 =
              let uu____9687 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9687  in
            aux uu____9684 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9693;
               FStar_Syntax_Syntax.vars = uu____9694;_},uu____9695::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____9698);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____9699;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____9700;_},uu____9701)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9784 =
              let uu____9787 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9787  in
            aux uu____9784 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____9793) ->
            let bs = FStar_List.rev out  in
            let uu____9835 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____9835 with
             | (bs1,t2) ->
                 let uu____9844 = patterns t2  in
                 (match uu____9844 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____9886 -> FStar_Pervasives_Native.None  in
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
      let uu____9958 = un_squash t  in
      FStar_Util.bind_opt uu____9958
        (fun t1  ->
           let uu____9974 = head_and_args' t1  in
           match uu____9974 with
           | (hd1,args) ->
               let uu____10007 =
                 let uu____10012 =
                   let uu____10013 = un_uinst hd1  in
                   uu____10013.FStar_Syntax_Syntax.n  in
                 (uu____10012, (FStar_List.length args))  in
               (match uu____10007 with
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
                | uu____10032 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____10061 = un_squash t  in
      FStar_Util.bind_opt uu____10061
        (fun t1  ->
           let uu____10076 = arrow_one t1  in
           match uu____10076 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____10091 =
                 let uu____10092 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____10092  in
               if uu____10091
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____10099 = comp_to_comp_typ_nouniv c  in
                    uu____10099.FStar_Syntax_Syntax.result_typ  in
                  let uu____10100 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____10100
                  then
                    let uu____10103 = patterns q  in
                    match uu____10103 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____10155 =
                       let uu____10156 =
                         let uu____10161 =
                           let uu____10162 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____10169 =
                             let uu____10178 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____10178]  in
                           uu____10162 :: uu____10169  in
                         (FStar_Parser_Const.imp_lid, uu____10161)  in
                       BaseConn uu____10156  in
                     FStar_Pervasives_Native.Some uu____10155))
           | uu____10203 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____10211 = un_squash t  in
      FStar_Util.bind_opt uu____10211
        (fun t1  ->
           let uu____10242 = head_and_args' t1  in
           match uu____10242 with
           | (hd1,args) ->
               let uu____10275 =
                 let uu____10288 =
                   let uu____10289 = un_uinst hd1  in
                   uu____10289.FStar_Syntax_Syntax.n  in
                 (uu____10288, args)  in
               (match uu____10275 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____10304)::(a2,uu____10306)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____10341 =
                      let uu____10342 = FStar_Syntax_Subst.compress a2  in
                      uu____10342.FStar_Syntax_Syntax.n  in
                    (match uu____10341 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____10349) ->
                         let uu____10376 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____10376 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____10415 -> failwith "impossible"  in
                              let uu____10420 = patterns q1  in
                              (match uu____10420 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____10471 -> FStar_Pervasives_Native.None)
                | uu____10472 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____10493 = destruct_sq_forall phi  in
          (match uu____10493 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____10507 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____10513 = destruct_sq_exists phi  in
          (match uu____10513 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____10527 -> f1)
      | uu____10530 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____10534 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____10534
      (fun uu____10539  ->
         let uu____10540 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____10540
           (fun uu____10545  ->
              let uu____10546 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____10546
                (fun uu____10551  ->
                   let uu____10552 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____10552
                     (fun uu____10557  ->
                        let uu____10558 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____10558
                          (fun uu____10562  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____10574 =
      let uu____10575 = FStar_Syntax_Subst.compress t  in
      uu____10575.FStar_Syntax_Syntax.n  in
    match uu____10574 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____10582) ->
        let uu____10609 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____10609 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____10635 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____10635
             then
               let uu____10638 =
                 let uu____10647 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____10647]  in
               mk_app t uu____10638
             else e1)
    | uu____10667 ->
        let uu____10668 =
          let uu____10677 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____10677]  in
        mk_app t uu____10668
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____10712 =
            let uu____10717 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____10717  in
          let uu____10718 =
            let uu____10719 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____10719  in
          let uu____10722 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____10712 a.FStar_Syntax_Syntax.action_univs uu____10718
            FStar_Parser_Const.effect_Tot_lid uu____10722 [] pos
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
    let reify_ =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
       in
    let uu____10745 =
      let uu____10752 =
        let uu____10753 =
          let uu____10768 =
            let uu____10777 = FStar_Syntax_Syntax.as_arg t  in [uu____10777]
             in
          (reify_, uu____10768)  in
        FStar_Syntax_Syntax.Tm_app uu____10753  in
      FStar_Syntax_Syntax.mk uu____10752  in
    uu____10745 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10815 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____10839 = unfold_lazy i  in delta_qualifier uu____10839
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____10841 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____10842 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____10843 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____10866 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____10879 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____10880 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____10887 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____10888 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____10902) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____10907;
           FStar_Syntax_Syntax.index = uu____10908;
           FStar_Syntax_Syntax.sort = t2;_},uu____10910)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____10918) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____10924,uu____10925) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____10967) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____10988,t2,uu____10990) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____11011,t2) -> delta_qualifier t2
  
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
    let uu____11042 = delta_qualifier t  in incr_delta_depth uu____11042
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11048 =
      let uu____11049 = FStar_Syntax_Subst.compress t  in
      uu____11049.FStar_Syntax_Syntax.n  in
    match uu____11048 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____11052 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____11066 =
      let uu____11081 = unmeta e  in head_and_args uu____11081  in
    match uu____11066 with
    | (head1,args) ->
        let uu____11108 =
          let uu____11121 =
            let uu____11122 = un_uinst head1  in
            uu____11122.FStar_Syntax_Syntax.n  in
          (uu____11121, args)  in
        (match uu____11108 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11138) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____11158::(hd1,uu____11160)::(tl1,uu____11162)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____11209 =
               let uu____11212 =
                 let uu____11215 = list_elements tl1  in
                 FStar_Util.must uu____11215  in
               hd1 :: uu____11212  in
             FStar_Pervasives_Native.Some uu____11209
         | uu____11224 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____11245 .
    ('Auu____11245 -> 'Auu____11245) ->
      'Auu____11245 Prims.list -> 'Auu____11245 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____11270 = f a  in [uu____11270]
      | x::xs -> let uu____11275 = apply_last f xs  in x :: uu____11275
  
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
          let uu____11321 =
            let uu____11328 =
              let uu____11329 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____11329  in
            FStar_Syntax_Syntax.mk uu____11328  in
          uu____11321 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____11346 =
            let uu____11351 =
              let uu____11352 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____11352
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____11351 args  in
          uu____11346 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____11368 =
            let uu____11373 =
              let uu____11374 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____11374
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____11373 args  in
          uu____11368 FStar_Pervasives_Native.None pos  in
        let uu____11377 =
          let uu____11378 =
            let uu____11379 = FStar_Syntax_Syntax.iarg typ  in [uu____11379]
             in
          nil uu____11378 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____11407 =
                 let uu____11408 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____11415 =
                   let uu____11424 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____11431 =
                     let uu____11440 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____11440]  in
                   uu____11424 :: uu____11431  in
                 uu____11408 :: uu____11415  in
               cons1 uu____11407 t.FStar_Syntax_Syntax.pos) l uu____11377
  
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
        | uu____11534 -> false
  
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
          | uu____11641 -> false
  
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
        | uu____11796 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____11830 = FStar_ST.op_Bang debug_term_eq  in
          if uu____11830
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
        let t11 = let uu____12014 = unmeta_safe t1  in canon_app uu____12014
           in
        let t21 = let uu____12020 = unmeta_safe t2  in canon_app uu____12020
           in
        let uu____12023 =
          let uu____12028 =
            let uu____12029 =
              let uu____12032 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____12032  in
            uu____12029.FStar_Syntax_Syntax.n  in
          let uu____12033 =
            let uu____12034 =
              let uu____12037 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____12037  in
            uu____12034.FStar_Syntax_Syntax.n  in
          (uu____12028, uu____12033)  in
        match uu____12023 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____12038,uu____12039) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12046,FStar_Syntax_Syntax.Tm_uinst uu____12047) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____12054,uu____12055) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12078,FStar_Syntax_Syntax.Tm_delayed uu____12079) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____12102,uu____12103) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12130,FStar_Syntax_Syntax.Tm_ascribed uu____12131) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____12164 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____12164
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____12167 = FStar_Const.eq_const c1 c2  in
            check "const" uu____12167
        | (FStar_Syntax_Syntax.Tm_type
           uu____12168,FStar_Syntax_Syntax.Tm_type uu____12169) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____12218 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____12218) &&
              (let uu____12224 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____12224)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____12263 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____12263) &&
              (let uu____12269 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____12269)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____12283 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____12283)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____12330 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____12330) &&
              (let uu____12332 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____12332)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____12417 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____12417) &&
              (let uu____12419 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____12419)
        | (FStar_Syntax_Syntax.Tm_lazy uu____12434,uu____12435) ->
            let uu____12436 =
              let uu____12437 = unlazy t11  in
              term_eq_dbg dbg uu____12437 t21  in
            check "lazy_l" uu____12436
        | (uu____12438,FStar_Syntax_Syntax.Tm_lazy uu____12439) ->
            let uu____12440 =
              let uu____12441 = unlazy t21  in
              term_eq_dbg dbg t11 uu____12441  in
            check "lazy_r" uu____12440
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____12477 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____12477))
              &&
              (let uu____12479 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____12479)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____12481),FStar_Syntax_Syntax.Tm_uvar (u2,uu____12483)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (check "tm_quoted qi" (qi1 = qi2)) &&
              (let uu____12539 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____12539)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____12566 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____12566) &&
                   (let uu____12568 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____12568)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____12585 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____12585) &&
                    (let uu____12587 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____12587))
                   &&
                   (let uu____12589 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____12589)
             | uu____12590 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____12595) -> fail "unk"
        | (uu____12596,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____12597,uu____12598) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____12599,uu____12600) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____12601,uu____12602) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____12603,uu____12604) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____12605,uu____12606) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____12607,uu____12608) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____12625,uu____12626) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____12639,uu____12640) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____12647,uu____12648) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____12663,uu____12664) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____12687,uu____12688) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____12701,uu____12702) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____12715,uu____12716) ->
            fail "bottom"
        | (uu____12723,FStar_Syntax_Syntax.Tm_bvar uu____12724) ->
            fail "bottom"
        | (uu____12725,FStar_Syntax_Syntax.Tm_name uu____12726) ->
            fail "bottom"
        | (uu____12727,FStar_Syntax_Syntax.Tm_fvar uu____12728) ->
            fail "bottom"
        | (uu____12729,FStar_Syntax_Syntax.Tm_constant uu____12730) ->
            fail "bottom"
        | (uu____12731,FStar_Syntax_Syntax.Tm_type uu____12732) ->
            fail "bottom"
        | (uu____12733,FStar_Syntax_Syntax.Tm_abs uu____12734) ->
            fail "bottom"
        | (uu____12751,FStar_Syntax_Syntax.Tm_arrow uu____12752) ->
            fail "bottom"
        | (uu____12765,FStar_Syntax_Syntax.Tm_refine uu____12766) ->
            fail "bottom"
        | (uu____12773,FStar_Syntax_Syntax.Tm_app uu____12774) ->
            fail "bottom"
        | (uu____12789,FStar_Syntax_Syntax.Tm_match uu____12790) ->
            fail "bottom"
        | (uu____12813,FStar_Syntax_Syntax.Tm_let uu____12814) ->
            fail "bottom"
        | (uu____12827,FStar_Syntax_Syntax.Tm_uvar uu____12828) ->
            fail "bottom"
        | (uu____12841,FStar_Syntax_Syntax.Tm_meta uu____12842) ->
            fail "bottom"

and (arg_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun dbg  ->
    fun a1  ->
      fun a2  ->
        eqprod
          (fun t1  ->
             fun t2  ->
               let uu____12869 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____12869)
          (fun q1  -> fun q2  -> check "arg qual" (q1 = q2)) a1 a2

and (binder_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun dbg  ->
    fun b1  ->
      fun b2  ->
        eqprod
          (fun b11  ->
             fun b21  ->
               let uu____12890 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____12890)
          (fun q1  -> fun q2  -> check "binder qual" (q1 = q2)) b1 b2

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
        ((let uu____12910 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____12910) &&
           (let uu____12912 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____12912))
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
    fun uu____12917  ->
      fun uu____12918  ->
        match (uu____12917, uu____12918) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____13043 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____13043) &&
               (let uu____13045 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____13045))
              &&
              (let uu____13047 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____13086 -> false  in
               check "branch when" uu____13047)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____13104 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____13104) &&
           (let uu____13110 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____13110))
          &&
          (let uu____13112 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____13112)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____13124 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____13124 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13169 ->
        let uu____13192 =
          let uu____13193 = FStar_Syntax_Subst.compress t  in
          sizeof uu____13193  in
        (Prims.parse_int "1") + uu____13192
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____13195 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____13195
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____13197 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____13197
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____13204 = sizeof t1  in (FStar_List.length us) + uu____13204
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____13207) ->
        let uu____13228 = sizeof t1  in
        let uu____13229 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____13240  ->
                 match uu____13240 with
                 | (bv,uu____13246) ->
                     let uu____13247 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____13247) (Prims.parse_int "0") bs
           in
        uu____13228 + uu____13229
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____13270 = sizeof hd1  in
        let uu____13271 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____13282  ->
                 match uu____13282 with
                 | (arg,uu____13288) ->
                     let uu____13289 = sizeof arg  in acc + uu____13289)
            (Prims.parse_int "0") args
           in
        uu____13270 + uu____13271
    | uu____13290 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____13301 =
        let uu____13302 = un_uinst t  in uu____13302.FStar_Syntax_Syntax.n
         in
      match uu____13301 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____13306 -> false
  
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
        let uu____13347 = FStar_Options.set_options t s  in
        match uu____13347 with
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
          ((let uu____13355 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____13355 (fun a236  -> ()));
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
  
let rec (unbound_variables :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun tm  ->
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13381 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____13407 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____13422 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____13423 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____13424 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____13433) ->
        let uu____13454 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____13454 with
         | (bs1,t2) ->
             let uu____13463 =
               FStar_List.collect
                 (fun uu____13473  ->
                    match uu____13473 with
                    | (b,uu____13481) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____13482 = unbound_variables t2  in
             FStar_List.append uu____13463 uu____13482)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____13503 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____13503 with
         | (bs1,c1) ->
             let uu____13512 =
               FStar_List.collect
                 (fun uu____13522  ->
                    match uu____13522 with
                    | (b,uu____13530) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____13531 = unbound_variables_comp c1  in
             FStar_List.append uu____13512 uu____13531)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____13540 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____13540 with
         | (bs,t2) ->
             let uu____13557 =
               FStar_List.collect
                 (fun uu____13567  ->
                    match uu____13567 with
                    | (b1,uu____13575) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____13576 = unbound_variables t2  in
             FStar_List.append uu____13557 uu____13576)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____13601 =
          FStar_List.collect
            (fun uu____13613  ->
               match uu____13613 with
               | (x,uu____13623) -> unbound_variables x) args
           in
        let uu____13628 = unbound_variables t1  in
        FStar_List.append uu____13601 uu____13628
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____13669 = unbound_variables t1  in
        let uu____13672 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____13687 = FStar_Syntax_Subst.open_branch br  in
                  match uu____13687 with
                  | (p,wopt,t2) ->
                      let uu____13709 = unbound_variables t2  in
                      let uu____13712 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____13709 uu____13712))
           in
        FStar_List.append uu____13669 uu____13672
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____13726) ->
        let uu____13767 = unbound_variables t1  in
        let uu____13770 =
          let uu____13773 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____13804 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____13773 uu____13804  in
        FStar_List.append uu____13767 uu____13770
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____13842 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____13845 =
          let uu____13848 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____13851 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____13856 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____13858 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____13858 with
                 | (uu____13873,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____13848 uu____13851  in
        FStar_List.append uu____13842 uu____13845
    | FStar_Syntax_Syntax.Tm_let ((uu____13875,lbs),t1) ->
        let uu____13892 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____13892 with
         | (lbs1,t2) ->
             let uu____13907 = unbound_variables t2  in
             let uu____13910 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____13917 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____13920 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____13917 uu____13920) lbs1
                in
             FStar_List.append uu____13907 uu____13910)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____13937 = unbound_variables t1  in
        let uu____13940 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____13973  ->
                      match uu____13973 with
                      | (a,uu____13983) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____13988,uu____13989,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____13995,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____14001 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____14008 -> []
          | FStar_Syntax_Syntax.Meta_named uu____14009 -> []  in
        FStar_List.append uu____13937 uu____13940

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____14016) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____14026) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____14036 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____14039 =
          FStar_List.collect
            (fun uu____14051  ->
               match uu____14051 with
               | (a,uu____14061) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____14036 uu____14039
