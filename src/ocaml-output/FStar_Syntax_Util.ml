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
      let uu____91 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____91 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____97 =
      let uu____100 =
        let uu____103 =
          FStar_Ident.mk_ident
            ((Prims.strcat FStar_Ident.reserved_prefix
                (Prims.strcat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____103]  in
      FStar_List.append lid.FStar_Ident.ns uu____100  in
    FStar_Ident.lid_of_ids uu____97
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____114 .
    (FStar_Syntax_Syntax.bv,'Auu____114) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term,'Auu____114) FStar_Pervasives_Native.tuple2
  =
  fun uu____127  ->
    match uu____127 with
    | (b,imp) ->
        let uu____134 = FStar_Syntax_Syntax.bv_to_name b  in (uu____134, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____159 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____159
            then []
            else (let uu____171 = arg_of_non_null_binder b  in [uu____171])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  =
  fun binders  ->
    let uu____197 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____243 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____243
              then
                let b1 =
                  let uu____261 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____261, (FStar_Pervasives_Native.snd b))  in
                let uu____262 = arg_of_non_null_binder b1  in (b1, uu____262)
              else
                (let uu____276 = arg_of_non_null_binder b  in (b, uu____276))))
       in
    FStar_All.pipe_right uu____197 FStar_List.unzip
  
let (name_binders :
  FStar_Syntax_Syntax.binder Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____360 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____360
              then
                let uu____365 = b  in
                match uu____365 with
                | (a,imp) ->
                    let b1 =
                      let uu____373 =
                        let uu____374 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____374  in
                      FStar_Ident.id_of_text uu____373  in
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
        let uu____408 =
          let uu____413 =
            let uu____414 =
              let uu____427 = name_binders binders  in (uu____427, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____414  in
          FStar_Syntax_Syntax.mk uu____413  in
        uu____408 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____445 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____487  ->
            match uu____487 with
            | (t,imp) ->
                let uu____498 =
                  let uu____499 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____499
                   in
                (uu____498, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____551  ->
            match uu____551 with
            | (t,imp) ->
                let uu____568 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____568, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____580 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____580
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____591 . 'Auu____591 -> 'Auu____591 Prims.list =
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
          (fun uu____687  ->
             fun uu____688  ->
               match (uu____687, uu____688) with
               | ((x,uu____706),(y,uu____708)) ->
                   let uu____717 =
                     let uu____724 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____724)  in
                   FStar_Syntax_Syntax.NT uu____717) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____733) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____739,uu____740) -> unmeta e2
    | uu____781 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____794 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____801 -> e1
         | uu____810 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____812,uu____813) ->
        unmeta_safe e2
    | uu____854 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____868 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____869 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____879 = univ_kernel u1  in
        (match uu____879 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____890 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____897 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____907 = univ_kernel u  in FStar_Pervasives_Native.snd uu____907
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____922,uu____923) ->
          failwith "Impossible: compare_univs"
      | (uu____924,FStar_Syntax_Syntax.U_bvar uu____925) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____926) ->
          ~- (Prims.parse_int "1")
      | (uu____927,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____928) -> ~- (Prims.parse_int "1")
      | (uu____929,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____932,FStar_Syntax_Syntax.U_unif
         uu____933) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____942,FStar_Syntax_Syntax.U_name
         uu____943) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____970 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____971 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____970 - uu____971
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____1002 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____1002
                 (fun uu____1017  ->
                    match uu____1017 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1031,uu____1032) ->
          ~- (Prims.parse_int "1")
      | (uu____1035,FStar_Syntax_Syntax.U_max uu____1036) ->
          (Prims.parse_int "1")
      | uu____1039 ->
          let uu____1044 = univ_kernel u1  in
          (match uu____1044 with
           | (k1,n1) ->
               let uu____1051 = univ_kernel u2  in
               (match uu____1051 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1070 = compare_univs u1 u2  in
      uu____1070 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1085 =
        let uu____1086 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1086;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1085
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1103 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1112 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1134 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1143 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1169 =
          let uu____1170 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1170  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1169;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1197 =
          let uu____1198 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1198  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1197;
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
      let uu___52_1231 = c  in
      let uu____1232 =
        let uu____1233 =
          let uu___53_1234 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___53_1234.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___53_1234.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___53_1234.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___53_1234.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1233  in
      {
        FStar_Syntax_Syntax.n = uu____1232;
        FStar_Syntax_Syntax.pos = (uu___52_1231.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___52_1231.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1254 -> c
        | FStar_Syntax_Syntax.GTotal uu____1263 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___54_1274 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___54_1274.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___54_1274.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___54_1274.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___54_1274.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___55_1275 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___55_1275.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___55_1275.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1278  ->
           let uu____1279 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1279)
  
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
    | uu____1314 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1325 -> true
    | FStar_Syntax_Syntax.GTotal uu____1334 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___40_1355  ->
               match uu___40_1355 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1356 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___41_1365  ->
               match uu___41_1365 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1366 -> false)))
  
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
            (fun uu___42_1375  ->
               match uu___42_1375 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1376 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___43_1389  ->
            match uu___43_1389 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1390 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___44_1399  ->
            match uu___44_1399 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1400 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1424 -> true
    | FStar_Syntax_Syntax.GTotal uu____1433 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___45_1446  ->
                   match uu___45_1446 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1447 -> false)))
  
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
let (is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___46_1475  ->
               match uu___46_1475 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1476 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1487 =
      let uu____1488 = FStar_Syntax_Subst.compress t  in
      uu____1488.FStar_Syntax_Syntax.n  in
    match uu____1487 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1491,c) -> is_pure_or_ghost_comp c
    | uu____1509 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1520 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1526 =
      let uu____1527 = FStar_Syntax_Subst.compress t  in
      uu____1527.FStar_Syntax_Syntax.n  in
    match uu____1526 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1530,c) -> is_lemma_comp c
    | uu____1548 -> false
  
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
    | uu____1615 -> (t1, [])
  
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
        let uu____1682 = head_and_args' head1  in
        (match uu____1682 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1739 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1761) ->
        FStar_Syntax_Subst.compress t2
    | uu____1766 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1772 =
      let uu____1773 = FStar_Syntax_Subst.compress t  in
      uu____1773.FStar_Syntax_Syntax.n  in
    match uu____1772 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1776,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1798)::uu____1799 ->
                  let pats' = unmeta pats  in
                  let uu____1843 = head_and_args pats'  in
                  (match uu____1843 with
                   | (head1,uu____1859) ->
                       let uu____1880 =
                         let uu____1881 = un_uinst head1  in
                         uu____1881.FStar_Syntax_Syntax.n  in
                       (match uu____1880 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1885 -> false))
              | uu____1886 -> false)
         | uu____1895 -> false)
    | uu____1896 -> false
  
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
                (fun uu___47_1910  ->
                   match uu___47_1910 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1911 -> false)))
    | uu____1912 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1927) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1937) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____1961 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____1970 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___56_1982 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___56_1982.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___56_1982.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___56_1982.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___56_1982.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___48_1995  ->
            match uu___48_1995 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____1996 -> false))
  
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
    | uu____2016 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2024,uu____2025) ->
        unascribe e2
    | uu____2066 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2118,uu____2119) ->
          ascribe t' k
      | uu____2160 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2186 =
      let uu____2193 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2193  in
    uu____2186 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2252 =
      let uu____2253 = FStar_Syntax_Subst.compress t  in
      uu____2253.FStar_Syntax_Syntax.n  in
    match uu____2252 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2257 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2257
    | uu____2258 -> t
  
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
            let uu____2297 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2297;
              FStar_Syntax_Syntax.lkind = k;
              FStar_Syntax_Syntax.typ = typ;
              FStar_Syntax_Syntax.rng = rng
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i)
            FStar_Pervasives_Native.None rng
  
let (canon_app :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____2305 =
      let uu____2318 = unascribe t  in head_and_args' uu____2318  in
    match uu____2305 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown [@@deriving show]
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2344 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2350 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2356 -> false
  
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
      let equal_if uu___49_2431 = if uu___49_2431 then Equal else Unknown  in
      let equal_iff uu___50_2437 = if uu___50_2437 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2453 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2463) -> NotEqual
        | (uu____2464,NotEqual ) -> NotEqual
        | (Unknown ,uu____2465) -> Unknown
        | (uu____2466,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____2508 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2508
        then
          let uu____2509 = ()  in
          let uu____2510 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2568  ->
                    match uu____2568 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2593 = ()  in
                        let uu____2594 = eq_tm a1 a2  in
                        eq_inj acc uu____2594) Equal) uu____2510
        else NotEqual  in
      let uu____2596 =
        let uu____2601 =
          let uu____2602 = unmeta t11  in uu____2602.FStar_Syntax_Syntax.n
           in
        let uu____2605 =
          let uu____2606 = unmeta t21  in uu____2606.FStar_Syntax_Syntax.n
           in
        (uu____2601, uu____2605)  in
      match uu____2596 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2611,uu____2612) ->
          let uu____2613 = unlazy t11  in eq_tm uu____2613 t21
      | (uu____2614,FStar_Syntax_Syntax.Tm_lazy uu____2615) ->
          let uu____2616 = unlazy t21  in eq_tm t11 uu____2616
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
            (let uu____2634 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2634)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2647 = eq_tm f g  in
          eq_and uu____2647
            (fun uu____2650  ->
               let uu____2651 = eq_univs_list us vs  in equal_if uu____2651)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2652),uu____2653) -> Unknown
      | (uu____2654,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2655)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2658 = FStar_Const.eq_const c d  in equal_iff uu____2658
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2660),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2662)) ->
          let uu____2711 = FStar_Syntax_Unionfind.equiv u1 u2  in
          equal_if uu____2711
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2756 =
            let uu____2761 =
              let uu____2762 = un_uinst h1  in
              uu____2762.FStar_Syntax_Syntax.n  in
            let uu____2765 =
              let uu____2766 = un_uinst h2  in
              uu____2766.FStar_Syntax_Syntax.n  in
            (uu____2761, uu____2765)  in
          (match uu____2756 with
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
                 (let uu____2778 =
                    let uu____2779 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____2779  in
                  FStar_List.mem uu____2778 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____2780 ->
               let uu____2785 = eq_tm h1 h2  in
               eq_and uu____2785 (fun uu____2787  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____2892 = FStar_List.zip bs1 bs2  in
            let uu____2955 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____2992  ->
                 fun a  ->
                   match uu____2992 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3085  -> branch_matches b1 b2))
              uu____2892 uu____2955
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3089 = eq_univs u v1  in equal_if uu____3089
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) -> if q1 = q2 then eq_tm t12 t22 else Unknown
      | uu____3103 -> Unknown

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
        | (uu____3183,uu____3184) -> false  in
      let uu____3193 = b1  in
      match uu____3193 with
      | (p1,w1,t1) ->
          let uu____3227 = b2  in
          (match uu____3227 with
           | (p2,w2,t2) ->
               let uu____3261 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3261
               then
                 let uu____3262 =
                   (let uu____3265 = eq_tm t1 t2  in uu____3265 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3274 = eq_tm t11 t21  in
                             uu____3274 = Equal) w1 w2)
                    in
                 (if uu____3262 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3308)::a11,(b,uu____3311)::b1) ->
          let uu____3365 = eq_tm a b  in
          (match uu____3365 with
           | Equal  -> eq_args a11 b1
           | uu____3366 -> Unknown)
      | uu____3367 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3381) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3387,uu____3388) ->
        unrefine t2
    | uu____3429 -> t1
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3435 =
      let uu____3436 = unrefine t  in uu____3436.FStar_Syntax_Syntax.n  in
    match uu____3435 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3441) -> is_unit t1
    | uu____3446 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3452 =
      let uu____3453 = unrefine t  in uu____3453.FStar_Syntax_Syntax.n  in
    match uu____3452 with
    | FStar_Syntax_Syntax.Tm_type uu____3456 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3459) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3481) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3486,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3504 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____3510 =
      let uu____3511 = FStar_Syntax_Subst.compress e  in
      uu____3511.FStar_Syntax_Syntax.n  in
    match uu____3510 with
    | FStar_Syntax_Syntax.Tm_abs uu____3514 -> true
    | uu____3531 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3537 =
      let uu____3538 = FStar_Syntax_Subst.compress t  in
      uu____3538.FStar_Syntax_Syntax.n  in
    match uu____3537 with
    | FStar_Syntax_Syntax.Tm_arrow uu____3541 -> true
    | uu____3554 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3562) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3568,uu____3569) ->
        pre_typ t2
    | uu____3610 -> t1
  
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
      let uu____3632 =
        let uu____3633 = un_uinst typ1  in uu____3633.FStar_Syntax_Syntax.n
         in
      match uu____3632 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____3688 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____3712 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____3730,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____3737) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____3742,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3753,uu____3754,uu____3755,uu____3756,uu____3757) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____3767,uu____3768,uu____3769,uu____3770) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____3776,uu____3777,uu____3778,uu____3779,uu____3780) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3786,uu____3787) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3789,uu____3790) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3793 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____3794 -> []
    | FStar_Syntax_Syntax.Sig_main uu____3795 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____3808 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___51_3831  ->
    match uu___51_3831 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____3844 'Auu____3845 .
    ('Auu____3844 FStar_Syntax_Syntax.syntax,'Auu____3845)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____3856  ->
    match uu____3856 with | (hd1,uu____3864) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____3877 'Auu____3878 .
    ('Auu____3877 FStar_Syntax_Syntax.syntax,'Auu____3878)
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
      | uu____3969 ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args))
            FStar_Pervasives_Native.None r
  
let (mk_data :
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term FStar_Syntax_Syntax.syntax)
  =
  fun l  ->
    fun args  ->
      match args with
      | [] ->
          let uu____4025 = FStar_Ident.range_of_lid l  in
          let uu____4026 =
            let uu____4031 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____4031  in
          uu____4026 FStar_Pervasives_Native.None uu____4025
      | uu____4035 ->
          let e =
            let uu____4047 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____4047 args  in
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
      let uu____4062 =
        let uu____4067 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____4067, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____4062
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
          let uu____4118 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____4118
          then
            let uu____4119 =
              let uu____4124 =
                let uu____4125 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____4125  in
              let uu____4126 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____4124, uu____4126)  in
            FStar_Ident.mk_ident uu____4119
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___57_4129 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___57_4129.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___57_4129.FStar_Syntax_Syntax.sort)
          }  in
        let uu____4130 = mk_field_projector_name_from_ident lid nm  in
        (uu____4130, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4141) -> ses
    | uu____4150 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____4159 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____4170 = FStar_Syntax_Unionfind.find uv  in
      match uu____4170 with
      | FStar_Pervasives_Native.Some uu____4173 ->
          let uu____4174 =
            let uu____4175 =
              let uu____4176 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____4176  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4175  in
          failwith uu____4174
      | uu____4177 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____4252 -> q1 = q2
  
let (abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        let close_lopt lopt1 =
          match lopt1 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rc ->
              let uu____4290 =
                let uu___58_4291 = rc  in
                let uu____4292 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___58_4291.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____4292;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___58_4291.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____4290
           in
        match bs with
        | [] -> t
        | uu____4303 ->
            let body =
              let uu____4305 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4305  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4333 =
                   let uu____4338 =
                     let uu____4339 =
                       let uu____4356 =
                         let uu____4363 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4363 bs'  in
                       let uu____4374 = close_lopt lopt'  in
                       (uu____4356, t1, uu____4374)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4339  in
                   FStar_Syntax_Syntax.mk uu____4338  in
                 uu____4333 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4390 ->
                 let uu____4397 =
                   let uu____4402 =
                     let uu____4403 =
                       let uu____4420 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4421 = close_lopt lopt  in
                       (uu____4420, body, uu____4421)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4403  in
                   FStar_Syntax_Syntax.mk uu____4402  in
                 uu____4397 FStar_Pervasives_Native.None
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
      | uu____4463 ->
          let uu____4470 =
            let uu____4475 =
              let uu____4476 =
                let uu____4489 = FStar_Syntax_Subst.close_binders bs  in
                let uu____4490 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____4489, uu____4490)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4476  in
            FStar_Syntax_Syntax.mk uu____4475  in
          uu____4470 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____4525 =
        let uu____4526 = FStar_Syntax_Subst.compress t  in
        uu____4526.FStar_Syntax_Syntax.n  in
      match uu____4525 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____4552) ->
               let uu____4561 =
                 let uu____4562 = FStar_Syntax_Subst.compress tres  in
                 uu____4562.FStar_Syntax_Syntax.n  in
               (match uu____4561 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____4597 -> t)
           | uu____4598 -> t)
      | uu____4599 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____4612 =
        let uu____4613 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____4613 t.FStar_Syntax_Syntax.pos  in
      let uu____4614 =
        let uu____4619 =
          let uu____4620 =
            let uu____4627 =
              let uu____4628 =
                let uu____4629 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____4629]  in
              FStar_Syntax_Subst.close uu____4628 t  in
            (b, uu____4627)  in
          FStar_Syntax_Syntax.Tm_refine uu____4620  in
        FStar_Syntax_Syntax.mk uu____4619  in
      uu____4614 FStar_Pervasives_Native.None uu____4612
  
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
        let uu____4682 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____4682 with
         | (bs1,c1) ->
             let uu____4699 = is_total_comp c1  in
             if uu____4699
             then
               let uu____4710 = arrow_formals_comp (comp_result c1)  in
               (match uu____4710 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____4756;
           FStar_Syntax_Syntax.index = uu____4757;
           FStar_Syntax_Syntax.sort = k2;_},uu____4759)
        -> arrow_formals_comp k2
    | uu____4766 ->
        let uu____4767 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4767)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____4795 = arrow_formals_comp k  in
    match uu____4795 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____4875 =
            let uu___59_4876 = rc  in
            let uu____4877 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___59_4876.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____4877;
              FStar_Syntax_Syntax.residual_flags =
                (uu___59_4876.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____4875
      | uu____4884 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____4914 =
        let uu____4915 =
          let uu____4918 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____4918  in
        uu____4915.FStar_Syntax_Syntax.n  in
      match uu____4914 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____4956 = aux t2 what  in
          (match uu____4956 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____5016 -> ([], t1, abs_body_lcomp)  in
    let uu____5029 = aux t FStar_Pervasives_Native.None  in
    match uu____5029 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____5071 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____5071 with
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
      FStar_Ident.ident Prims.list ->
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
                    | (FStar_Pervasives_Native.None ,uu____5232) -> def
                    | (uu____5243,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____5255) ->
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
      FStar_Syntax_Syntax.comp ->
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
            let uu____5361 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____5361 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5390 ->
            let t' = arrow binders c  in
            let uu____5400 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5400 with
             | (uvs1,t'1) ->
                 let uu____5419 =
                   let uu____5420 = FStar_Syntax_Subst.compress t'1  in
                   uu____5420.FStar_Syntax_Syntax.n  in
                 (match uu____5419 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____5461 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____5480 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____5487 -> false
  
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
      let uu____5535 =
        let uu____5536 = pre_typ t  in uu____5536.FStar_Syntax_Syntax.n  in
      match uu____5535 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____5540 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____5551 =
        let uu____5552 = pre_typ t  in uu____5552.FStar_Syntax_Syntax.n  in
      match uu____5551 with
      | FStar_Syntax_Syntax.Tm_fvar uu____5555 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____5557) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5579) ->
          is_constructed_typ t1 lid
      | uu____5584 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____5595 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____5596 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____5597 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5599) -> get_tycon t2
    | uu____5620 -> FStar_Pervasives_Native.None
  
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
    let uu____5634 =
      let uu____5635 = un_uinst t  in uu____5635.FStar_Syntax_Syntax.n  in
    match uu____5634 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____5639 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____5646 =
        let uu____5649 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____5649  in
      match uu____5646 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____5662 -> false
    else false
  
let (ktype : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (ktype0 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (type_u :
  unit ->
    (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5678  ->
    let u =
      let uu____5684 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_5  -> FStar_Syntax_Syntax.U_unif _0_5)
        uu____5684
       in
    let uu____5701 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____5701, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____5716 = eq_tm a a'  in
      match uu____5716 with | Equal  -> true | uu____5717 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____5720 =
    let uu____5725 =
      let uu____5726 =
        let uu____5727 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____5727
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____5726  in
    FStar_Syntax_Syntax.mk uu____5725  in
  uu____5720 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (exp_true_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_false_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_unit : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
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
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
      FStar_Pervasives_Native.None
  
let (tand : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.and_lid 
let (tor : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.or_lid 
let (timp : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (tiff : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
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
let (mk_conj_opt :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu____5786 =
            let uu____5789 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____5790 =
              let uu____5795 =
                let uu____5796 =
                  let uu____5811 =
                    let uu____5814 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____5815 =
                      let uu____5818 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____5818]  in
                    uu____5814 :: uu____5815  in
                  (tand, uu____5811)  in
                FStar_Syntax_Syntax.Tm_app uu____5796  in
              FStar_Syntax_Syntax.mk uu____5795  in
            uu____5790 FStar_Pervasives_Native.None uu____5789  in
          FStar_Pervasives_Native.Some uu____5786
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____5847 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____5848 =
          let uu____5853 =
            let uu____5854 =
              let uu____5869 =
                let uu____5872 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____5873 =
                  let uu____5876 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____5876]  in
                uu____5872 :: uu____5873  in
              (op_t, uu____5869)  in
            FStar_Syntax_Syntax.Tm_app uu____5854  in
          FStar_Syntax_Syntax.mk uu____5853  in
        uu____5848 FStar_Pervasives_Native.None uu____5847
  
let (mk_neg :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____5891 =
      let uu____5896 =
        let uu____5897 =
          let uu____5912 =
            let uu____5915 = FStar_Syntax_Syntax.as_arg phi  in [uu____5915]
             in
          (t_not, uu____5912)  in
        FStar_Syntax_Syntax.Tm_app uu____5897  in
      FStar_Syntax_Syntax.mk uu____5896  in
    uu____5891 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
let (mk_conj :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tand phi1 phi2 
let (mk_conj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term) =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
  
let (mk_disj :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tor phi1 phi2 
let (mk_disj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term) =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
  
let (mk_imp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop timp phi1 phi2 
let (mk_iff :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop tiff phi1 phi2 
let (b2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e  ->
    let uu____5998 =
      let uu____6003 =
        let uu____6004 =
          let uu____6019 =
            let uu____6022 = FStar_Syntax_Syntax.as_arg e  in [uu____6022]
             in
          (b2t_v, uu____6019)  in
        FStar_Syntax_Syntax.Tm_app uu____6004  in
      FStar_Syntax_Syntax.mk uu____6003  in
    uu____5998 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____6040 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____6041 =
        let uu____6046 =
          let uu____6047 =
            let uu____6062 =
              let uu____6065 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____6066 =
                let uu____6069 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____6069]  in
              uu____6065 :: uu____6066  in
            (teq, uu____6062)  in
          FStar_Syntax_Syntax.Tm_app uu____6047  in
        FStar_Syntax_Syntax.mk uu____6046  in
      uu____6041 FStar_Pervasives_Native.None uu____6040
  
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
          let uu____6096 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____6097 =
            let uu____6102 =
              let uu____6103 =
                let uu____6118 =
                  let uu____6121 = FStar_Syntax_Syntax.iarg t  in
                  let uu____6122 =
                    let uu____6125 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____6126 =
                      let uu____6129 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____6129]  in
                    uu____6125 :: uu____6126  in
                  uu____6121 :: uu____6122  in
                (eq_inst, uu____6118)  in
              FStar_Syntax_Syntax.Tm_app uu____6103  in
            FStar_Syntax_Syntax.mk uu____6102  in
          uu____6097 FStar_Pervasives_Native.None uu____6096
  
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
        let uu____6158 =
          let uu____6163 =
            let uu____6164 =
              let uu____6179 =
                let uu____6182 = FStar_Syntax_Syntax.iarg t  in
                let uu____6183 =
                  let uu____6186 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____6187 =
                    let uu____6190 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____6190]  in
                  uu____6186 :: uu____6187  in
                uu____6182 :: uu____6183  in
              (t_has_type1, uu____6179)  in
            FStar_Syntax_Syntax.Tm_app uu____6164  in
          FStar_Syntax_Syntax.mk uu____6163  in
        uu____6158 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        let t_with_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst (t_with_type, [u]))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        let uu____6221 =
          let uu____6226 =
            let uu____6227 =
              let uu____6242 =
                let uu____6245 = FStar_Syntax_Syntax.iarg t  in
                let uu____6246 =
                  let uu____6249 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____6249]  in
                uu____6245 :: uu____6246  in
              (t_with_type1, uu____6242)  in
            FStar_Syntax_Syntax.Tm_app uu____6227  in
          FStar_Syntax_Syntax.mk uu____6226  in
        uu____6221 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu____6259 =
    let uu____6264 =
      let uu____6265 =
        let uu____6272 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____6272, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____6265  in
    FStar_Syntax_Syntax.mk uu____6264  in
  uu____6259 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (lex_pair : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (tforall : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (t_haseq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
  
let (lcomp_of_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.lcomp)
  =
  fun c0  ->
    let uu____6287 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____6300 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____6311 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____6287 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____6332  -> c0)
  
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
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fa  ->
    fun x  ->
      fun body  ->
        let uu____6406 =
          let uu____6411 =
            let uu____6412 =
              let uu____6427 =
                let uu____6430 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____6431 =
                  let uu____6434 =
                    let uu____6435 =
                      let uu____6436 =
                        let uu____6437 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____6437]  in
                      abs uu____6436 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____6435  in
                  [uu____6434]  in
                uu____6430 :: uu____6431  in
              (fa, uu____6427)  in
            FStar_Syntax_Syntax.Tm_app uu____6412  in
          FStar_Syntax_Syntax.mk uu____6411  in
        uu____6406 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____6490 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____6490
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____6501 -> true
    | uu____6502 -> false
  
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
          let uu____6547 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____6547, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____6575 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____6575, FStar_Pervasives_Native.None, t2)  in
        let uu____6588 =
          let uu____6589 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____6589  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____6588
  
let (mk_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
          FStar_Pervasives_Native.None
         in
      let uu____6663 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6666 =
        let uu____6675 = FStar_Syntax_Syntax.as_arg p  in [uu____6675]  in
      mk_app uu____6663 uu____6666
  
let (mk_auto_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
          FStar_Pervasives_Native.None
         in
      let uu____6689 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6692 =
        let uu____6701 = FStar_Syntax_Syntax.as_arg p  in [uu____6701]  in
      mk_app uu____6689 uu____6692
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6711 = head_and_args t  in
    match uu____6711 with
    | (head1,args) ->
        let uu____6752 =
          let uu____6765 =
            let uu____6766 = un_uinst head1  in
            uu____6766.FStar_Syntax_Syntax.n  in
          (uu____6765, args)  in
        (match uu____6752 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____6783)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____6835 =
                    let uu____6840 =
                      let uu____6841 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____6841]  in
                    FStar_Syntax_Subst.open_term uu____6840 p  in
                  (match uu____6835 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____6870 -> failwith "impossible"  in
                       let uu____6875 =
                         let uu____6876 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____6876
                          in
                       if uu____6875
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____6886 -> FStar_Pervasives_Native.None)
         | uu____6889 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6917 = head_and_args t  in
    match uu____6917 with
    | (head1,args) ->
        let uu____6962 =
          let uu____6975 =
            let uu____6976 = FStar_Syntax_Subst.compress head1  in
            uu____6976.FStar_Syntax_Syntax.n  in
          (uu____6975, args)  in
        (match uu____6962 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____6996;
               FStar_Syntax_Syntax.vars = uu____6997;_},u::[]),(t1,uu____7000)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____7039 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7071 = head_and_args t  in
    match uu____7071 with
    | (head1,args) ->
        let uu____7116 =
          let uu____7129 =
            let uu____7130 = FStar_Syntax_Subst.compress head1  in
            uu____7130.FStar_Syntax_Syntax.n  in
          (uu____7129, args)  in
        (match uu____7116 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____7150;
               FStar_Syntax_Syntax.vars = uu____7151;_},u::[]),(t1,uu____7154)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____7193 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____7217 = let uu____7232 = unmeta t  in head_and_args uu____7232
       in
    match uu____7217 with
    | (head1,uu____7234) ->
        let uu____7255 =
          let uu____7256 = un_uinst head1  in
          uu____7256.FStar_Syntax_Syntax.n  in
        (match uu____7255 with
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
         | uu____7260 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7278 =
      let uu____7291 =
        let uu____7292 = FStar_Syntax_Subst.compress t  in
        uu____7292.FStar_Syntax_Syntax.n  in
      match uu____7291 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____7401 =
            let uu____7410 =
              let uu____7411 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____7411  in
            (b, uu____7410)  in
          FStar_Pervasives_Native.Some uu____7401
      | uu____7424 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____7278
      (fun uu____7460  ->
         match uu____7460 with
         | (b,c) ->
             let uu____7495 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____7495 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____7542 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____7569 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____7569
  
type qpats = FStar_Syntax_Syntax.args Prims.list[@@deriving show]
type connective =
  | QAll of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3 
  | QEx of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3 
  | BaseConn of (FStar_Ident.lident,FStar_Syntax_Syntax.args)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____7614 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____7652 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____7688 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____7724) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____7736) ->
          unmeta_monadic t
      | uu____7749 -> f2  in
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
      let aux f2 uu____7830 =
        match uu____7830 with
        | (lid,arity) ->
            let uu____7839 =
              let uu____7854 = unmeta_monadic f2  in head_and_args uu____7854
               in
            (match uu____7839 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____7880 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____7880
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____7956 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____7956)
      | uu____7967 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____8018 = head_and_args t1  in
        match uu____8018 with
        | (t2,args) ->
            let uu____8065 = un_uinst t2  in
            let uu____8066 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____8099  ->
                      match uu____8099 with
                      | (t3,imp) ->
                          let uu____8110 = unascribe t3  in (uu____8110, imp)))
               in
            (uu____8065, uu____8066)
         in
      let rec aux qopt out t1 =
        let uu____8148 = let uu____8165 = flat t1  in (qopt, uu____8165)  in
        match uu____8148 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____8192;
                 FStar_Syntax_Syntax.vars = uu____8193;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____8196);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____8197;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____8198;_},uu____8199)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____8276;
                 FStar_Syntax_Syntax.vars = uu____8277;_},uu____8278::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____8281);
                  FStar_Syntax_Syntax.pos = uu____8282;
                  FStar_Syntax_Syntax.vars = uu____8283;_},uu____8284)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____8372;
               FStar_Syntax_Syntax.vars = uu____8373;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____8376);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8377;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8378;_},uu____8379)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____8450 =
              let uu____8453 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____8453  in
            aux uu____8450 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____8459;
               FStar_Syntax_Syntax.vars = uu____8460;_},uu____8461::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____8464);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____8465;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____8466;_},uu____8467)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____8550 =
              let uu____8553 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____8553  in
            aux uu____8550 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____8559) ->
            let bs = FStar_List.rev out  in
            let uu____8593 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____8593 with
             | (bs1,t2) ->
                 let uu____8602 = patterns t2  in
                 (match uu____8602 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____8664 -> FStar_Pervasives_Native.None  in
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
      let uu____8731 = un_squash t  in
      FStar_Util.bind_opt uu____8731
        (fun t1  ->
           let uu____8747 = head_and_args' t1  in
           match uu____8747 with
           | (hd1,args) ->
               let uu____8780 =
                 let uu____8785 =
                   let uu____8786 = un_uinst hd1  in
                   uu____8786.FStar_Syntax_Syntax.n  in
                 (uu____8785, (FStar_List.length args))  in
               (match uu____8780 with
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
                | uu____8869 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____8895 = un_squash t  in
      FStar_Util.bind_opt uu____8895
        (fun t1  ->
           let uu____8910 = arrow_one t1  in
           match uu____8910 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____8925 =
                 let uu____8926 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____8926  in
               if uu____8925
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____8933 = comp_to_comp_typ_nouniv c  in
                    uu____8933.FStar_Syntax_Syntax.result_typ  in
                  let uu____8934 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____8934
                  then
                    let uu____8937 = patterns q  in
                    match uu____8937 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____8993 =
                       let uu____8994 =
                         let uu____8999 =
                           let uu____9002 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____9003 =
                             let uu____9006 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____9006]  in
                           uu____9002 :: uu____9003  in
                         (FStar_Parser_Const.imp_lid, uu____8999)  in
                       BaseConn uu____8994  in
                     FStar_Pervasives_Native.Some uu____8993))
           | uu____9009 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____9017 = un_squash t  in
      FStar_Util.bind_opt uu____9017
        (fun t1  ->
           let uu____9048 = head_and_args' t1  in
           match uu____9048 with
           | (hd1,args) ->
               let uu____9081 =
                 let uu____9094 =
                   let uu____9095 = un_uinst hd1  in
                   uu____9095.FStar_Syntax_Syntax.n  in
                 (uu____9094, args)  in
               (match uu____9081 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____9110)::(a2,uu____9112)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____9147 =
                      let uu____9148 = FStar_Syntax_Subst.compress a2  in
                      uu____9148.FStar_Syntax_Syntax.n  in
                    (match uu____9147 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____9155) ->
                         let uu____9182 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____9182 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____9221 -> failwith "impossible"  in
                              let uu____9226 = patterns q1  in
                              (match uu____9226 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____9293 -> FStar_Pervasives_Native.None)
                | uu____9294 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____9315 = destruct_sq_forall phi  in
          (match uu____9315 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____9337 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____9343 = destruct_sq_exists phi  in
          (match uu____9343 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____9365 -> f1)
      | uu____9368 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____9372 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____9372
      (fun uu____9377  ->
         let uu____9378 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____9378
           (fun uu____9383  ->
              let uu____9384 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____9384
                (fun uu____9389  ->
                   let uu____9390 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____9390
                     (fun uu____9395  ->
                        let uu____9396 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____9396
                          (fun uu____9400  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____9408 =
      let uu____9409 = FStar_Syntax_Subst.compress t  in
      uu____9409.FStar_Syntax_Syntax.n  in
    match uu____9408 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____9416) ->
        let uu____9443 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____9443 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____9469 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____9469
             then
               let uu____9472 =
                 let uu____9481 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____9481]  in
               mk_app t uu____9472
             else e1)
    | uu____9483 ->
        let uu____9484 =
          let uu____9493 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____9493]  in
        mk_app t uu____9484
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____9510 =
            let uu____9515 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.Delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____9515  in
          let uu____9516 =
            let uu____9517 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____9517  in
          let uu____9520 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____9510 a.FStar_Syntax_Syntax.action_univs uu____9516
            FStar_Parser_Const.effect_Tot_lid uu____9520 [] pos
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
    let uu____9549 =
      let uu____9554 =
        let uu____9555 =
          let uu____9570 =
            let uu____9573 = FStar_Syntax_Syntax.as_arg t  in [uu____9573]
             in
          (reify_, uu____9570)  in
        FStar_Syntax_Syntax.Tm_app uu____9555  in
      FStar_Syntax_Syntax.mk uu____9554  in
    uu____9549 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____9587 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____9613 = unfold_lazy i  in delta_qualifier uu____9613
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____9615 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____9616 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____9617 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____9640 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____9657 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____9658 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____9665 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____9666 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____9680) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____9685;
           FStar_Syntax_Syntax.index = uu____9686;
           FStar_Syntax_Syntax.sort = t2;_},uu____9688)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____9696) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____9702,uu____9703) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____9745) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____9766,t2,uu____9768) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____9789,t2) -> delta_qualifier t2
  
let rec (incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth) =
  fun d  ->
    match d with
    | FStar_Syntax_Syntax.Delta_equational  -> d
    | FStar_Syntax_Syntax.Delta_constant  ->
        FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        FStar_Syntax_Syntax.Delta_defined_at_level
          (i + (Prims.parse_int "1"))
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
  
let (incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let uu____9819 = delta_qualifier t  in incr_delta_depth uu____9819
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9825 =
      let uu____9826 = FStar_Syntax_Subst.compress t  in
      uu____9826.FStar_Syntax_Syntax.n  in
    match uu____9825 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____9829 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9843 = let uu____9858 = unmeta e  in head_and_args uu____9858
       in
    match uu____9843 with
    | (head1,args) ->
        let uu____9885 =
          let uu____9898 =
            let uu____9899 = un_uinst head1  in
            uu____9899.FStar_Syntax_Syntax.n  in
          (uu____9898, args)  in
        (match uu____9885 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9915) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____9935::(hd1,uu____9937)::(tl1,uu____9939)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____9986 =
               let uu____9991 =
                 let uu____9996 = list_elements tl1  in
                 FStar_Util.must uu____9996  in
               hd1 :: uu____9991  in
             FStar_Pervasives_Native.Some uu____9986
         | uu____10009 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____10030 .
    ('Auu____10030 -> 'Auu____10030) ->
      'Auu____10030 Prims.list -> 'Auu____10030 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____10055 = f a  in [uu____10055]
      | x::xs -> let uu____10060 = apply_last f xs  in x :: uu____10060
  
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
          let uu____10105 =
            let uu____10110 =
              let uu____10111 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____10111  in
            FStar_Syntax_Syntax.mk uu____10110  in
          uu____10105 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____10126 =
            let uu____10129 =
              let uu____10130 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____10130
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____10129 args  in
          uu____10126 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____10144 =
            let uu____10147 =
              let uu____10148 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____10148
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____10147 args  in
          uu____10144 FStar_Pervasives_Native.None pos  in
        let uu____10151 =
          let uu____10152 =
            let uu____10153 = FStar_Syntax_Syntax.iarg typ  in [uu____10153]
             in
          nil uu____10152 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____10159 =
                 let uu____10160 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____10161 =
                   let uu____10164 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____10165 =
                     let uu____10168 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____10168]  in
                   uu____10164 :: uu____10165  in
                 uu____10160 :: uu____10161  in
               cons1 uu____10159 t.FStar_Syntax_Syntax.pos) l uu____10151
  
let (uvar_from_id :
  Prims.int ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun id1  ->
    fun t  ->
      let uu____10181 =
        let uu____10186 =
          let uu____10187 =
            let uu____10204 = FStar_Syntax_Unionfind.from_id id1  in
            (uu____10204, t)  in
          FStar_Syntax_Syntax.Tm_uvar uu____10187  in
        FStar_Syntax_Syntax.mk uu____10186  in
      uu____10181 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        | uu____10271 -> false
  
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
          | uu____10378 -> false
  
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
        | uu____10533 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        (let uu____10566 =
           let uu____10567 = FStar_ST.op_Bang debug_term_eq  in
           if uu____10567
           then FStar_Util.print1 ">>> term_eq failing: %s\n" msg
           else ()  in
         false)
  
let (fail : Prims.string -> Prims.bool) = fun msg  -> check msg false 
let rec (term_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun dbg  ->
    fun t1  ->
      fun t2  ->
        let t11 = let uu____10755 = unmeta_safe t1  in canon_app uu____10755
           in
        let t21 = let uu____10759 = unmeta_safe t2  in canon_app uu____10759
           in
        let uu____10760 =
          let uu____10765 =
            let uu____10766 =
              let uu____10769 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____10769  in
            uu____10766.FStar_Syntax_Syntax.n  in
          let uu____10770 =
            let uu____10771 =
              let uu____10774 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____10774  in
            uu____10771.FStar_Syntax_Syntax.n  in
          (uu____10765, uu____10770)  in
        match uu____10760 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____10775,uu____10776) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10783,FStar_Syntax_Syntax.Tm_uinst uu____10784) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____10791,uu____10792) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10817,FStar_Syntax_Syntax.Tm_delayed uu____10818) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____10843,uu____10844) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10871,FStar_Syntax_Syntax.Tm_ascribed uu____10872) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____10905 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____10905
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____10908 = FStar_Const.eq_const c1 c2  in
            check "const" uu____10908
        | (FStar_Syntax_Syntax.Tm_type
           uu____10909,FStar_Syntax_Syntax.Tm_type uu____10910) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____10959 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____10959) &&
              (let uu____10965 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____10965)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____11004 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____11004) &&
              (let uu____11010 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____11010)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____11024 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____11024)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____11071 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____11071) &&
              (let uu____11073 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____11073)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____11158 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____11158) &&
              (let uu____11160 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____11160)
        | (FStar_Syntax_Syntax.Tm_lazy uu____11175,uu____11176) ->
            let uu____11177 =
              let uu____11178 = unlazy t11  in
              term_eq_dbg dbg uu____11178 t21  in
            check "lazy_l" uu____11177
        | (uu____11179,FStar_Syntax_Syntax.Tm_lazy uu____11180) ->
            let uu____11181 =
              let uu____11182 = unlazy t21  in
              term_eq_dbg dbg t11 uu____11182  in
            check "lazy_r" uu____11181
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____11218 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____11218))
              &&
              (let uu____11220 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____11220)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____11222),FStar_Syntax_Syntax.Tm_uvar (u2,uu____11224)) ->
            check "uvar" (u1 = u2)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (check "tm_quoted qi" (qi1 = qi2)) &&
              (let uu____11296 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____11296)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____11323 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____11323) &&
                   (let uu____11325 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____11325)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____11342 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____11342) &&
                    (let uu____11344 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____11344))
                   &&
                   (let uu____11346 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____11346)
             | uu____11347 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____11352) -> fail "unk"
        | (uu____11353,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____11354,uu____11355) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____11356,uu____11357) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____11358,uu____11359) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____11360,uu____11361) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____11362,uu____11363) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____11364,uu____11365) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____11382,uu____11383) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____11396,uu____11397) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____11404,uu____11405) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____11420,uu____11421) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____11444,uu____11445) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____11458,uu____11459) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____11476,uu____11477) ->
            fail "bottom"
        | (uu____11484,FStar_Syntax_Syntax.Tm_bvar uu____11485) ->
            fail "bottom"
        | (uu____11486,FStar_Syntax_Syntax.Tm_name uu____11487) ->
            fail "bottom"
        | (uu____11488,FStar_Syntax_Syntax.Tm_fvar uu____11489) ->
            fail "bottom"
        | (uu____11490,FStar_Syntax_Syntax.Tm_constant uu____11491) ->
            fail "bottom"
        | (uu____11492,FStar_Syntax_Syntax.Tm_type uu____11493) ->
            fail "bottom"
        | (uu____11494,FStar_Syntax_Syntax.Tm_abs uu____11495) ->
            fail "bottom"
        | (uu____11512,FStar_Syntax_Syntax.Tm_arrow uu____11513) ->
            fail "bottom"
        | (uu____11526,FStar_Syntax_Syntax.Tm_refine uu____11527) ->
            fail "bottom"
        | (uu____11534,FStar_Syntax_Syntax.Tm_app uu____11535) ->
            fail "bottom"
        | (uu____11550,FStar_Syntax_Syntax.Tm_match uu____11551) ->
            fail "bottom"
        | (uu____11574,FStar_Syntax_Syntax.Tm_let uu____11575) ->
            fail "bottom"
        | (uu____11588,FStar_Syntax_Syntax.Tm_uvar uu____11589) ->
            fail "bottom"
        | (uu____11606,FStar_Syntax_Syntax.Tm_meta uu____11607) ->
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
               let uu____11634 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____11634)
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
               let uu____11655 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____11655)
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
        ((let uu____11675 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____11675) &&
           (let uu____11677 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____11677))
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
    fun uu____11682  ->
      fun uu____11683  ->
        match (uu____11682, uu____11683) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____11808 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____11808) &&
               (let uu____11810 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____11810))
              &&
              (let uu____11812 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____11851 -> false  in
               check "branch when" uu____11812)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____11869 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____11869) &&
           (let uu____11875 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____11875))
          &&
          (let uu____11877 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____11877)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____11889 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____11889 t1 t2  in
      let uu____11913 = FStar_ST.op_Colon_Equals debug_term_eq false  in r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11942 ->
        let uu____11967 =
          let uu____11968 = FStar_Syntax_Subst.compress t  in
          sizeof uu____11968  in
        (Prims.parse_int "1") + uu____11967
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____11970 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____11970
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____11972 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____11972
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____11979 = sizeof t1  in (FStar_List.length us) + uu____11979
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____11982) ->
        let uu____12003 = sizeof t1  in
        let uu____12004 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____12015  ->
                 match uu____12015 with
                 | (bv,uu____12021) ->
                     let uu____12022 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____12022) (Prims.parse_int "0") bs
           in
        uu____12003 + uu____12004
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____12045 = sizeof hd1  in
        let uu____12046 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____12057  ->
                 match uu____12057 with
                 | (arg,uu____12063) ->
                     let uu____12064 = sizeof arg  in acc + uu____12064)
            (Prims.parse_int "0") args
           in
        uu____12045 + uu____12046
    | uu____12065 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____12076 =
        let uu____12077 = un_uinst t  in uu____12077.FStar_Syntax_Syntax.n
         in
      match uu____12076 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____12081 -> false
  
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
        let uu____12120 = FStar_Options.set_options t s  in
        match uu____12120 with
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
          let uu____12127 =
            let uu____12128 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____12128
              (fun a245  -> (Obj.magic ()) a245)
             in
          (match sopt with
           | FStar_Pervasives_Native.None  -> ()
           | FStar_Pervasives_Native.Some s ->
               set_options1 FStar_Options.Reset s)
  
let rec (unbound_variables :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv Prims.list) =
  fun tm  ->
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____12148 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____12204 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____12205 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____12206 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____12215) ->
        let uu____12236 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____12236 with
         | (bs1,t2) ->
             let uu____12245 =
               FStar_List.collect
                 (fun uu____12255  ->
                    match uu____12255 with
                    | (b,uu____12263) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____12264 = unbound_variables t2  in
             FStar_List.append uu____12245 uu____12264)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____12285 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____12285 with
         | (bs1,c1) ->
             let uu____12294 =
               FStar_List.collect
                 (fun uu____12304  ->
                    match uu____12304 with
                    | (b,uu____12312) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____12313 = unbound_variables_comp c1  in
             FStar_List.append uu____12294 uu____12313)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____12322 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____12322 with
         | (bs,t2) ->
             let uu____12345 =
               FStar_List.collect
                 (fun uu____12355  ->
                    match uu____12355 with
                    | (b1,uu____12363) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____12364 = unbound_variables t2  in
             FStar_List.append uu____12345 uu____12364)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____12389 =
          FStar_List.collect
            (fun uu____12399  ->
               match uu____12399 with
               | (x,uu____12407) -> unbound_variables x) args
           in
        let uu____12408 = unbound_variables t1  in
        FStar_List.append uu____12389 uu____12408
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____12449 = unbound_variables t1  in
        let uu____12452 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____12481 = FStar_Syntax_Subst.open_branch br  in
                  match uu____12481 with
                  | (p,wopt,t2) ->
                      let uu____12503 = unbound_variables t2  in
                      let uu____12506 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____12503 uu____12506))
           in
        FStar_List.append uu____12449 uu____12452
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____12520) ->
        let uu____12561 = unbound_variables t1  in
        let uu____12564 =
          let uu____12567 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____12598 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____12567 uu____12598  in
        FStar_List.append uu____12561 uu____12564
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____12636 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____12639 =
          let uu____12642 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____12645 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____12650 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____12652 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____12652 with
                 | (uu____12673,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____12642 uu____12645  in
        FStar_List.append uu____12636 uu____12639
    | FStar_Syntax_Syntax.Tm_let ((uu____12675,lbs),t1) ->
        let uu____12692 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____12692 with
         | (lbs1,t2) ->
             let uu____12707 = unbound_variables t2  in
             let uu____12710 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____12717 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____12720 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____12717 uu____12720) lbs1
                in
             FStar_List.append uu____12707 uu____12710)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____12737 = unbound_variables t1  in
        let uu____12740 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____12769  ->
                      match uu____12769 with
                      | (a,uu____12777) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____12778,uu____12779,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____12785,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____12791 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____12798 -> []
          | FStar_Syntax_Syntax.Meta_named uu____12799 -> []  in
        FStar_List.append uu____12737 uu____12740

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.bv Prims.list) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____12804) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____12814) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____12824 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____12827 =
          FStar_List.collect
            (fun uu____12837  ->
               match uu____12837 with
               | (a,uu____12845) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____12824 uu____12827
