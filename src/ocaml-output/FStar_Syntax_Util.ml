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
  'Auu____115 .
    (FStar_Syntax_Syntax.bv,'Auu____115) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term,'Auu____115) FStar_Pervasives_Native.tuple2
  =
  fun uu____128  ->
    match uu____128 with
    | (b,imp) ->
        let uu____135 = FStar_Syntax_Syntax.bv_to_name b  in (uu____135, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____174 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____174
            then []
            else (let uu____186 = arg_of_non_null_binder b  in [uu____186])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  =
  fun binders  ->
    let uu____212 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____276 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____276
              then
                let b1 =
                  let uu____294 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____294, (FStar_Pervasives_Native.snd b))  in
                let uu____295 = arg_of_non_null_binder b1  in (b1, uu____295)
              else
                (let uu____309 = arg_of_non_null_binder b  in (b, uu____309))))
       in
    FStar_All.pipe_right uu____212 FStar_List.unzip
  
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
              let uu____409 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____409
              then
                let uu____414 = b  in
                match uu____414 with
                | (a,imp) ->
                    let b1 =
                      let uu____426 =
                        let uu____427 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____427  in
                      FStar_Ident.id_of_text uu____426  in
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
        let uu____461 =
          let uu____468 =
            let uu____469 =
              let uu____482 = name_binders binders  in (uu____482, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____469  in
          FStar_Syntax_Syntax.mk uu____468  in
        uu____461 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____500 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____536  ->
            match uu____536 with
            | (t,imp) ->
                let uu____547 =
                  let uu____548 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____548
                   in
                (uu____547, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____596  ->
            match uu____596 with
            | (t,imp) ->
                let uu____613 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____613, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____625 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____625
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____636 . 'Auu____636 -> 'Auu____636 Prims.list =
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
          (fun uu____732  ->
             fun uu____733  ->
               match (uu____732, uu____733) with
               | ((x,uu____751),(y,uu____753)) ->
                   let uu____762 =
                     let uu____769 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____769)  in
                   FStar_Syntax_Syntax.NT uu____762) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____782) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____788,uu____789) -> unmeta e2
    | uu____830 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____843 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____850 -> e1
         | uu____859 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____861,uu____862) ->
        unmeta_safe e2
    | uu____903 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____917 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____918 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____928 = univ_kernel u1  in
        (match uu____928 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____939 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____946 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____956 = univ_kernel u  in FStar_Pervasives_Native.snd uu____956
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____971,uu____972) ->
          failwith "Impossible: compare_univs"
      | (uu____973,FStar_Syntax_Syntax.U_bvar uu____974) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____975) ->
          ~- (Prims.parse_int "1")
      | (uu____976,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____977) -> ~- (Prims.parse_int "1")
      | (uu____978,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____981,FStar_Syntax_Syntax.U_unif
         uu____982) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____991,FStar_Syntax_Syntax.U_name
         uu____992) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____1019 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____1020 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____1019 - uu____1020
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____1051 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____1051
                 (fun uu____1066  ->
                    match uu____1066 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1080,uu____1081) ->
          ~- (Prims.parse_int "1")
      | (uu____1084,FStar_Syntax_Syntax.U_max uu____1085) ->
          (Prims.parse_int "1")
      | uu____1088 ->
          let uu____1093 = univ_kernel u1  in
          (match uu____1093 with
           | (k1,n1) ->
               let uu____1100 = univ_kernel u2  in
               (match uu____1100 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1119 = compare_univs u1 u2  in
      uu____1119 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1134 =
        let uu____1135 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1135;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1134
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1152 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1161 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1183 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1192 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1218 =
          let uu____1219 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1219  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1218;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1246 =
          let uu____1247 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1247  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1246;
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
      let uu___117_1280 = c  in
      let uu____1281 =
        let uu____1282 =
          let uu___118_1283 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___118_1283.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___118_1283.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___118_1283.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___118_1283.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1282  in
      {
        FStar_Syntax_Syntax.n = uu____1281;
        FStar_Syntax_Syntax.pos = (uu___117_1280.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___117_1280.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1308 -> c
        | FStar_Syntax_Syntax.GTotal uu____1317 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___119_1328 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___119_1328.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___119_1328.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___119_1328.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___119_1328.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___120_1329 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___120_1329.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___120_1329.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1332  ->
           let uu____1333 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1333)
  
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
    | uu____1368 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1379 -> true
    | FStar_Syntax_Syntax.GTotal uu____1388 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___105_1409  ->
               match uu___105_1409 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1410 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___106_1419  ->
               match uu___106_1419 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1420 -> false)))
  
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
            (fun uu___107_1429  ->
               match uu___107_1429 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1430 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___108_1443  ->
            match uu___108_1443 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1444 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___109_1453  ->
            match uu___109_1453 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1454 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1478 -> true
    | FStar_Syntax_Syntax.GTotal uu____1487 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___110_1500  ->
                   match uu___110_1500 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1501 -> false)))
  
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
            (fun uu___111_1534  ->
               match uu___111_1534 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1535 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1546 =
      let uu____1547 = FStar_Syntax_Subst.compress t  in
      uu____1547.FStar_Syntax_Syntax.n  in
    match uu____1546 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1550,c) -> is_pure_or_ghost_comp c
    | uu____1568 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1579 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1585 =
      let uu____1586 = FStar_Syntax_Subst.compress t  in
      uu____1586.FStar_Syntax_Syntax.n  in
    match uu____1585 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1589,c) -> is_lemma_comp c
    | uu____1607 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1613 =
      let uu____1614 = FStar_Syntax_Subst.compress t  in
      uu____1614.FStar_Syntax_Syntax.n  in
    match uu____1613 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1618) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____1640) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____1677,t1,uu____1679) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1701,uu____1702) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1744) -> head_of t1
    | uu____1749 -> t
  
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
    | uu____1816 -> (t1, [])
  
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
        let uu____1885 = head_and_args' head1  in
        (match uu____1885 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1942 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1964) ->
        FStar_Syntax_Subst.compress t2
    | uu____1969 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1975 =
      let uu____1976 = FStar_Syntax_Subst.compress t  in
      uu____1976.FStar_Syntax_Syntax.n  in
    match uu____1975 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1979,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____2001)::uu____2002 ->
                  let pats' = unmeta pats  in
                  let uu____2046 = head_and_args pats'  in
                  (match uu____2046 with
                   | (head1,uu____2062) ->
                       let uu____2083 =
                         let uu____2084 = un_uinst head1  in
                         uu____2084.FStar_Syntax_Syntax.n  in
                       (match uu____2083 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____2088 -> false))
              | uu____2089 -> false)
         | uu____2098 -> false)
    | uu____2099 -> false
  
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
                (fun uu___112_2113  ->
                   match uu___112_2113 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2114 -> false)))
    | uu____2115 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2130) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2140) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2168 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2177 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___121_2189 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___121_2189.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___121_2189.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___121_2189.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___121_2189.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2202  ->
           let uu____2203 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____2203 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___113_2218  ->
            match uu___113_2218 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2219 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2225 -> []
    | FStar_Syntax_Syntax.GTotal uu____2240 -> []
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
    | uu____2275 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2283,uu____2284) ->
        unascribe e2
    | uu____2325 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2377,uu____2378) ->
          ascribe t' k
      | uu____2419 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2445 =
      let uu____2454 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2454  in
    uu____2445 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2513 =
      let uu____2514 = FStar_Syntax_Subst.compress t  in
      uu____2514.FStar_Syntax_Syntax.n  in
    match uu____2513 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2518 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2518
    | uu____2519 -> t
  
let rec unlazy_as_t :
  'Auu____2526 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2526
  =
  fun k  ->
    fun t  ->
      let uu____2537 =
        let uu____2538 = FStar_Syntax_Subst.compress t  in
        uu____2538.FStar_Syntax_Syntax.n  in
      match uu____2537 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.typ = uu____2543;
            FStar_Syntax_Syntax.rng = uu____2544;_}
          when k = k' -> FStar_Dyn.undyn v1
      | uu____2547 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2586 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2586;
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
    let uu____2598 =
      let uu____2611 = unascribe t  in head_and_args' uu____2611  in
    match uu____2598 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2637 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2643 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2649 -> false
  
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
      let equal_if uu___114_2725 = if uu___114_2725 then Equal else Unknown
         in
      let equal_iff uu___115_2732 = if uu___115_2732 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2750 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2762) -> NotEqual
        | (uu____2763,NotEqual ) -> NotEqual
        | (Unknown ,uu____2764) -> Unknown
        | (uu____2765,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____2811 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2811
        then
          let uu____2813 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2871  ->
                    match uu____2871 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2897 = eq_tm a1 a2  in
                        eq_inj acc uu____2897) Equal) uu____2813
        else NotEqual  in
      let uu____2899 =
        let uu____2904 =
          let uu____2905 = unmeta t11  in uu____2905.FStar_Syntax_Syntax.n
           in
        let uu____2908 =
          let uu____2909 = unmeta t21  in uu____2909.FStar_Syntax_Syntax.n
           in
        (uu____2904, uu____2908)  in
      match uu____2899 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2914,uu____2915) ->
          let uu____2916 = unlazy t11  in eq_tm uu____2916 t21
      | (uu____2917,FStar_Syntax_Syntax.Tm_lazy uu____2918) ->
          let uu____2919 = unlazy t21  in eq_tm t11 uu____2919
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
            (let uu____2937 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2937)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2950 = eq_tm f g  in
          eq_and uu____2950
            (fun uu____2953  ->
               let uu____2954 = eq_univs_list us vs  in equal_if uu____2954)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2955),uu____2956) -> Unknown
      | (uu____2957,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2958)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2961 = FStar_Const.eq_const c d  in equal_iff uu____2961
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____2963)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____2965))) ->
          let uu____2994 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____2994
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3039 =
            let uu____3044 =
              let uu____3045 = un_uinst h1  in
              uu____3045.FStar_Syntax_Syntax.n  in
            let uu____3048 =
              let uu____3049 = un_uinst h2  in
              uu____3049.FStar_Syntax_Syntax.n  in
            (uu____3044, uu____3048)  in
          (match uu____3039 with
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
                 (let uu____3061 =
                    let uu____3062 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3062  in
                  FStar_List.mem uu____3061 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3063 ->
               let uu____3068 = eq_tm h1 h2  in
               eq_and uu____3068 (fun uu____3070  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3175 = FStar_List.zip bs1 bs2  in
            let uu____3238 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3275  ->
                 fun a  ->
                   match uu____3275 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3368  -> branch_matches b1 b2))
              uu____3175 uu____3238
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3372 = eq_univs u v1  in equal_if uu____3372
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) -> if q1 = q2 then eq_tm t12 t22 else Unknown
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____3398 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____3398 (fun uu____3400  -> eq_tm phi1 phi2)
      | uu____3401 -> Unknown

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
        | (uu____3484,uu____3485) -> false  in
      let uu____3494 = b1  in
      match uu____3494 with
      | (p1,w1,t1) ->
          let uu____3528 = b2  in
          (match uu____3528 with
           | (p2,w2,t2) ->
               let uu____3562 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3562
               then
                 let uu____3563 =
                   (let uu____3566 = eq_tm t1 t2  in uu____3566 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3575 = eq_tm t11 t21  in
                             uu____3575 = Equal) w1 w2)
                    in
                 (if uu____3563 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3625)::a11,(b,uu____3628)::b1) ->
          let uu____3682 = eq_tm a b  in
          (match uu____3682 with
           | Equal  -> eq_args a11 b1
           | uu____3683 -> Unknown)
      | uu____3684 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3714) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3720,uu____3721) ->
        unrefine t2
    | uu____3762 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3768 =
      let uu____3769 = FStar_Syntax_Subst.compress t  in
      uu____3769.FStar_Syntax_Syntax.n  in
    match uu____3768 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3772 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3786) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____3791 ->
        let uu____3806 =
          let uu____3807 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____3807 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____3806 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3861,uu____3862) ->
        is_uvar t1
    | uu____3903 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3909 =
      let uu____3910 = unrefine t  in uu____3910.FStar_Syntax_Syntax.n  in
    match uu____3909 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3915) -> is_unit t1
    | uu____3920 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3926 =
      let uu____3927 = unrefine t  in uu____3927.FStar_Syntax_Syntax.n  in
    match uu____3926 with
    | FStar_Syntax_Syntax.Tm_type uu____3930 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3933) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3955) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3960,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3978 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____3984 =
      let uu____3985 = FStar_Syntax_Subst.compress e  in
      uu____3985.FStar_Syntax_Syntax.n  in
    match uu____3984 with
    | FStar_Syntax_Syntax.Tm_abs uu____3988 -> true
    | uu____4005 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4011 =
      let uu____4012 = FStar_Syntax_Subst.compress t  in
      uu____4012.FStar_Syntax_Syntax.n  in
    match uu____4011 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4015 -> true
    | uu____4028 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4036) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4042,uu____4043) ->
        pre_typ t2
    | uu____4084 -> t1
  
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
      let uu____4106 =
        let uu____4107 = un_uinst typ1  in uu____4107.FStar_Syntax_Syntax.n
         in
      match uu____4106 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____4162 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____4186 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____4204,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____4211) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____4216,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____4227,uu____4228,uu____4229,uu____4230,uu____4231) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____4241,uu____4242,uu____4243,uu____4244) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____4250,uu____4251,uu____4252,uu____4253,uu____4254) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____4260,uu____4261) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4263,uu____4264) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____4267 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____4268 -> []
    | FStar_Syntax_Syntax.Sig_main uu____4269 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____4282 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___116_4305  ->
    match uu___116_4305 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____4318 'Auu____4319 .
    ('Auu____4318 FStar_Syntax_Syntax.syntax,'Auu____4319)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____4330  ->
    match uu____4330 with | (hd1,uu____4338) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____4351 'Auu____4352 .
    ('Auu____4351 FStar_Syntax_Syntax.syntax,'Auu____4352)
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
      | uu____4443 ->
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
          let uu____4503 = FStar_Ident.range_of_lid l  in
          let uu____4504 =
            let uu____4513 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____4513  in
          uu____4504 FStar_Pervasives_Native.None uu____4503
      | uu____4521 ->
          let e =
            let uu____4533 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____4533 args  in
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
      let uu____4548 =
        let uu____4553 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____4553, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____4548
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
          let uu____4604 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____4604
          then
            let uu____4605 =
              let uu____4610 =
                let uu____4611 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____4611  in
              let uu____4612 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____4610, uu____4612)  in
            FStar_Ident.mk_ident uu____4605
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___122_4615 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___122_4615.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___122_4615.FStar_Syntax_Syntax.sort)
          }  in
        let uu____4616 = mk_field_projector_name_from_ident lid nm  in
        (uu____4616, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4627) -> ses
    | uu____4636 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____4645 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____4656 = FStar_Syntax_Unionfind.find uv  in
      match uu____4656 with
      | FStar_Pervasives_Native.Some uu____4659 ->
          let uu____4660 =
            let uu____4661 =
              let uu____4662 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____4662  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4661  in
          failwith uu____4660
      | uu____4663 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____4738 -> q1 = q2
  
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
              let uu____4783 =
                let uu___123_4784 = rc  in
                let uu____4785 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___123_4784.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____4785;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___123_4784.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____4783
           in
        match bs with
        | [] -> t
        | uu____4800 ->
            let body =
              let uu____4802 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4802  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4832 =
                   let uu____4839 =
                     let uu____4840 =
                       let uu____4857 =
                         let uu____4864 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4864 bs'  in
                       let uu____4875 = close_lopt lopt'  in
                       (uu____4857, t1, uu____4875)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4840  in
                   FStar_Syntax_Syntax.mk uu____4839  in
                 uu____4832 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4891 ->
                 let uu____4898 =
                   let uu____4905 =
                     let uu____4906 =
                       let uu____4923 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4930 = close_lopt lopt  in
                       (uu____4923, body, uu____4930)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4906  in
                   FStar_Syntax_Syntax.mk uu____4905  in
                 uu____4898 FStar_Pervasives_Native.None
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
      | uu____4980 ->
          let uu____4987 =
            let uu____4994 =
              let uu____4995 =
                let uu____5008 = FStar_Syntax_Subst.close_binders bs  in
                let uu____5015 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____5008, uu____5015)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4995  in
            FStar_Syntax_Syntax.mk uu____4994  in
          uu____4987 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____5060 =
        let uu____5061 = FStar_Syntax_Subst.compress t  in
        uu____5061.FStar_Syntax_Syntax.n  in
      match uu____5060 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____5087) ->
               let uu____5096 =
                 let uu____5097 = FStar_Syntax_Subst.compress tres  in
                 uu____5097.FStar_Syntax_Syntax.n  in
               (match uu____5096 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____5132 -> t)
           | uu____5133 -> t)
      | uu____5134 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____5151 =
        let uu____5152 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____5152 t.FStar_Syntax_Syntax.pos  in
      let uu____5153 =
        let uu____5160 =
          let uu____5161 =
            let uu____5168 =
              let uu____5171 =
                let uu____5172 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____5172]  in
              FStar_Syntax_Subst.close uu____5171 t  in
            (b, uu____5168)  in
          FStar_Syntax_Syntax.Tm_refine uu____5161  in
        FStar_Syntax_Syntax.mk uu____5160  in
      uu____5153 FStar_Pervasives_Native.None uu____5151
  
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
        let uu____5239 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____5239 with
         | (bs1,c1) ->
             let uu____5256 = is_total_comp c1  in
             if uu____5256
             then
               let uu____5267 = arrow_formals_comp (comp_result c1)  in
               (match uu____5267 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____5319;
           FStar_Syntax_Syntax.index = uu____5320;
           FStar_Syntax_Syntax.sort = k2;_},uu____5322)
        -> arrow_formals_comp k2
    | uu____5329 ->
        let uu____5330 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____5330)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____5358 = arrow_formals_comp k  in
    match uu____5358 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____5440 =
            let uu___124_5441 = rc  in
            let uu____5442 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___124_5441.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____5442;
              FStar_Syntax_Syntax.residual_flags =
                (uu___124_5441.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____5440
      | uu____5451 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____5483 =
        let uu____5484 =
          let uu____5487 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____5487  in
        uu____5484.FStar_Syntax_Syntax.n  in
      match uu____5483 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____5527 = aux t2 what  in
          (match uu____5527 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____5587 -> ([], t1, abs_body_lcomp)  in
    let uu____5600 = aux t FStar_Pervasives_Native.None  in
    match uu____5600 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____5642 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____5642 with
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
                    | (FStar_Pervasives_Native.None ,uu____5803) -> def
                    | (uu____5814,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____5826) ->
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
            let uu____5912 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____5912 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5941 ->
            let t' = arrow binders c  in
            let uu____5951 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5951 with
             | (uvs1,t'1) ->
                 let uu____5970 =
                   let uu____5971 = FStar_Syntax_Subst.compress t'1  in
                   uu____5971.FStar_Syntax_Syntax.n  in
                 (match uu____5970 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____6012 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____6031 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____6038 -> false
  
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
      let uu____6086 =
        let uu____6087 = pre_typ t  in uu____6087.FStar_Syntax_Syntax.n  in
      match uu____6086 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____6091 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____6102 =
        let uu____6103 = pre_typ t  in uu____6103.FStar_Syntax_Syntax.n  in
      match uu____6102 with
      | FStar_Syntax_Syntax.Tm_fvar uu____6106 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____6108) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6130) ->
          is_constructed_typ t1 lid
      | uu____6135 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____6146 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____6147 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____6148 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____6150) -> get_tycon t2
    | uu____6171 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____6177 =
      let uu____6178 = un_uinst t  in uu____6178.FStar_Syntax_Syntax.n  in
    match uu____6177 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____6182 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____6189 =
        let uu____6192 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____6192  in
      match uu____6189 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____6205 -> false
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
  fun uu____6217  ->
    let u =
      let uu____6223 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_5  -> FStar_Syntax_Syntax.U_unif _0_5)
        uu____6223
       in
    let uu____6240 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____6240, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____6251 = eq_tm a a'  in
      match uu____6251 with | Equal  -> true | uu____6252 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____6255 =
    let uu____6262 =
      let uu____6263 =
        let uu____6264 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____6264
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____6263  in
    FStar_Syntax_Syntax.mk uu____6262  in
  uu____6255 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____6339 =
            let uu____6342 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____6343 =
              let uu____6350 =
                let uu____6351 =
                  let uu____6366 =
                    let uu____6375 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____6382 =
                      let uu____6391 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____6391]  in
                    uu____6375 :: uu____6382  in
                  (tand, uu____6366)  in
                FStar_Syntax_Syntax.Tm_app uu____6351  in
              FStar_Syntax_Syntax.mk uu____6350  in
            uu____6343 FStar_Pervasives_Native.None uu____6342  in
          FStar_Pervasives_Native.Some uu____6339
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____6460 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____6461 =
          let uu____6468 =
            let uu____6469 =
              let uu____6484 =
                let uu____6493 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____6500 =
                  let uu____6509 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____6509]  in
                uu____6493 :: uu____6500  in
              (op_t, uu____6484)  in
            FStar_Syntax_Syntax.Tm_app uu____6469  in
          FStar_Syntax_Syntax.mk uu____6468  in
        uu____6461 FStar_Pervasives_Native.None uu____6460
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____6558 =
      let uu____6565 =
        let uu____6566 =
          let uu____6581 =
            let uu____6590 = FStar_Syntax_Syntax.as_arg phi  in [uu____6590]
             in
          (t_not, uu____6581)  in
        FStar_Syntax_Syntax.Tm_app uu____6566  in
      FStar_Syntax_Syntax.mk uu____6565  in
    uu____6558 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____6775 =
      let uu____6782 =
        let uu____6783 =
          let uu____6798 =
            let uu____6807 = FStar_Syntax_Syntax.as_arg e  in [uu____6807]
             in
          (b2t_v, uu____6798)  in
        FStar_Syntax_Syntax.Tm_app uu____6783  in
      FStar_Syntax_Syntax.mk uu____6782  in
    uu____6775 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____6844 =
      let uu____6845 = unmeta t  in uu____6845.FStar_Syntax_Syntax.n  in
    match uu____6844 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____6849 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____6870 = is_t_true t1  in
      if uu____6870
      then t2
      else
        (let uu____6874 = is_t_true t2  in
         if uu____6874 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____6898 = is_t_true t1  in
      if uu____6898
      then t_true
      else
        (let uu____6902 = is_t_true t2  in
         if uu____6902 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____6926 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____6927 =
        let uu____6934 =
          let uu____6935 =
            let uu____6950 =
              let uu____6959 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____6966 =
                let uu____6975 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____6975]  in
              uu____6959 :: uu____6966  in
            (teq, uu____6950)  in
          FStar_Syntax_Syntax.Tm_app uu____6935  in
        FStar_Syntax_Syntax.mk uu____6934  in
      uu____6927 FStar_Pervasives_Native.None uu____6926
  
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
          let uu____7034 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____7035 =
            let uu____7042 =
              let uu____7043 =
                let uu____7058 =
                  let uu____7067 = FStar_Syntax_Syntax.iarg t  in
                  let uu____7074 =
                    let uu____7083 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____7090 =
                      let uu____7099 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____7099]  in
                    uu____7083 :: uu____7090  in
                  uu____7067 :: uu____7074  in
                (eq_inst, uu____7058)  in
              FStar_Syntax_Syntax.Tm_app uu____7043  in
            FStar_Syntax_Syntax.mk uu____7042  in
          uu____7035 FStar_Pervasives_Native.None uu____7034
  
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
        let uu____7166 =
          let uu____7173 =
            let uu____7174 =
              let uu____7189 =
                let uu____7198 = FStar_Syntax_Syntax.iarg t  in
                let uu____7205 =
                  let uu____7214 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____7221 =
                    let uu____7230 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____7230]  in
                  uu____7214 :: uu____7221  in
                uu____7198 :: uu____7205  in
              (t_has_type1, uu____7189)  in
            FStar_Syntax_Syntax.Tm_app uu____7174  in
          FStar_Syntax_Syntax.mk uu____7173  in
        uu____7166 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____7297 =
          let uu____7304 =
            let uu____7305 =
              let uu____7320 =
                let uu____7329 = FStar_Syntax_Syntax.iarg t  in
                let uu____7336 =
                  let uu____7345 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____7345]  in
                uu____7329 :: uu____7336  in
              (t_with_type1, uu____7320)  in
            FStar_Syntax_Syntax.Tm_app uu____7305  in
          FStar_Syntax_Syntax.mk uu____7304  in
        uu____7297 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____7383 =
    let uu____7390 =
      let uu____7391 =
        let uu____7398 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____7398, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____7391  in
    FStar_Syntax_Syntax.mk uu____7390  in
  uu____7383 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____7411 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____7424 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____7435 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____7411 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____7456  -> c0)
  
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
        let uu____7534 =
          let uu____7541 =
            let uu____7542 =
              let uu____7557 =
                let uu____7566 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____7573 =
                  let uu____7582 =
                    let uu____7589 =
                      let uu____7590 =
                        let uu____7591 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____7591]  in
                      abs uu____7590 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____7589  in
                  [uu____7582]  in
                uu____7566 :: uu____7573  in
              (fa, uu____7557)  in
            FStar_Syntax_Syntax.Tm_app uu____7542  in
          FStar_Syntax_Syntax.mk uu____7541  in
        uu____7534 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____7696 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____7696
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____7707 -> true
    | uu____7708 -> false
  
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
          let uu____7753 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____7753, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____7781 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____7781, FStar_Pervasives_Native.None, t2)  in
        let uu____7794 =
          let uu____7795 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____7795  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____7794
  
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
      let uu____7869 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7872 =
        let uu____7881 = FStar_Syntax_Syntax.as_arg p  in [uu____7881]  in
      mk_app uu____7869 uu____7872
  
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
      let uu____7913 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7916 =
        let uu____7925 = FStar_Syntax_Syntax.as_arg p  in [uu____7925]  in
      mk_app uu____7913 uu____7916
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7953 = head_and_args t  in
    match uu____7953 with
    | (head1,args) ->
        let uu____7994 =
          let uu____8007 =
            let uu____8008 = un_uinst head1  in
            uu____8008.FStar_Syntax_Syntax.n  in
          (uu____8007, args)  in
        (match uu____7994 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____8025)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____8077 =
                    let uu____8082 =
                      let uu____8083 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____8083]  in
                    FStar_Syntax_Subst.open_term uu____8082 p  in
                  (match uu____8077 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____8124 -> failwith "impossible"  in
                       let uu____8129 =
                         let uu____8130 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____8130
                          in
                       if uu____8129
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____8142 -> FStar_Pervasives_Native.None)
         | uu____8145 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8173 = head_and_args t  in
    match uu____8173 with
    | (head1,args) ->
        let uu____8218 =
          let uu____8231 =
            let uu____8232 = FStar_Syntax_Subst.compress head1  in
            uu____8232.FStar_Syntax_Syntax.n  in
          (uu____8231, args)  in
        (match uu____8218 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____8252;
               FStar_Syntax_Syntax.vars = uu____8253;_},u::[]),(t1,uu____8256)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____8293 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8325 = head_and_args t  in
    match uu____8325 with
    | (head1,args) ->
        let uu____8370 =
          let uu____8383 =
            let uu____8384 = FStar_Syntax_Subst.compress head1  in
            uu____8384.FStar_Syntax_Syntax.n  in
          (uu____8383, args)  in
        (match uu____8370 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____8404;
               FStar_Syntax_Syntax.vars = uu____8405;_},u::[]),(t1,uu____8408)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____8445 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8469 = let uu____8484 = unmeta t  in head_and_args uu____8484
       in
    match uu____8469 with
    | (head1,uu____8486) ->
        let uu____8507 =
          let uu____8508 = un_uinst head1  in
          uu____8508.FStar_Syntax_Syntax.n  in
        (match uu____8507 with
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
         | uu____8512 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8530 =
      let uu____8541 =
        let uu____8542 = FStar_Syntax_Subst.compress t  in
        uu____8542.FStar_Syntax_Syntax.n  in
      match uu____8541 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____8643 =
            let uu____8652 =
              let uu____8653 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____8653  in
            (b, uu____8652)  in
          FStar_Pervasives_Native.Some uu____8643
      | uu____8666 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____8530
      (fun uu____8698  ->
         match uu____8698 with
         | (b,c) ->
             let uu____8727 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____8727 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____8774 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____8801 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8801
  
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
    match projectee with | QAll _0 -> true | uu____8849 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____8887 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____8923 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____8960) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____8972) ->
          unmeta_monadic t
      | uu____8985 -> f2  in
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
      let aux f2 uu____9069 =
        match uu____9069 with
        | (lid,arity) ->
            let uu____9078 =
              let uu____9093 = unmeta_monadic f2  in head_and_args uu____9093
               in
            (match uu____9078 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____9119 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____9119
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____9188 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____9188)
      | uu____9199 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____9254 = head_and_args t1  in
        match uu____9254 with
        | (t2,args) ->
            let uu____9301 = un_uinst t2  in
            let uu____9302 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9333  ->
                      match uu____9333 with
                      | (t3,imp) ->
                          let uu____9344 = unascribe t3  in (uu____9344, imp)))
               in
            (uu____9301, uu____9302)
         in
      let rec aux qopt out t1 =
        let uu____9385 = let uu____9406 = flat t1  in (qopt, uu____9406)  in
        match uu____9385 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____9441;
                 FStar_Syntax_Syntax.vars = uu____9442;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____9445);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____9446;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____9447;_},uu____9448)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____9525;
                 FStar_Syntax_Syntax.vars = uu____9526;_},uu____9527::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____9530);
                  FStar_Syntax_Syntax.pos = uu____9531;
                  FStar_Syntax_Syntax.vars = uu____9532;_},uu____9533)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9621;
               FStar_Syntax_Syntax.vars = uu____9622;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____9625);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____9626;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____9627;_},uu____9628)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9699 =
              let uu____9702 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9702  in
            aux uu____9699 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9708;
               FStar_Syntax_Syntax.vars = uu____9709;_},uu____9710::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____9713);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____9714;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____9715;_},uu____9716)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9799 =
              let uu____9802 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9802  in
            aux uu____9799 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____9808) ->
            let bs = FStar_List.rev out  in
            let uu____9850 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____9850 with
             | (bs1,t2) ->
                 let uu____9859 = patterns t2  in
                 (match uu____9859 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____9901 -> FStar_Pervasives_Native.None  in
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
      let uu____9973 = un_squash t  in
      FStar_Util.bind_opt uu____9973
        (fun t1  ->
           let uu____9989 = head_and_args' t1  in
           match uu____9989 with
           | (hd1,args) ->
               let uu____10022 =
                 let uu____10027 =
                   let uu____10028 = un_uinst hd1  in
                   uu____10028.FStar_Syntax_Syntax.n  in
                 (uu____10027, (FStar_List.length args))  in
               (match uu____10022 with
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
                | uu____10047 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____10076 = un_squash t  in
      FStar_Util.bind_opt uu____10076
        (fun t1  ->
           let uu____10091 = arrow_one t1  in
           match uu____10091 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____10106 =
                 let uu____10107 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____10107  in
               if uu____10106
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____10114 = comp_to_comp_typ_nouniv c  in
                    uu____10114.FStar_Syntax_Syntax.result_typ  in
                  let uu____10115 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____10115
                  then
                    let uu____10118 = patterns q  in
                    match uu____10118 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____10170 =
                       let uu____10171 =
                         let uu____10176 =
                           let uu____10177 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____10184 =
                             let uu____10193 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____10193]  in
                           uu____10177 :: uu____10184  in
                         (FStar_Parser_Const.imp_lid, uu____10176)  in
                       BaseConn uu____10171  in
                     FStar_Pervasives_Native.Some uu____10170))
           | uu____10218 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____10226 = un_squash t  in
      FStar_Util.bind_opt uu____10226
        (fun t1  ->
           let uu____10257 = head_and_args' t1  in
           match uu____10257 with
           | (hd1,args) ->
               let uu____10290 =
                 let uu____10303 =
                   let uu____10304 = un_uinst hd1  in
                   uu____10304.FStar_Syntax_Syntax.n  in
                 (uu____10303, args)  in
               (match uu____10290 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____10319)::(a2,uu____10321)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____10356 =
                      let uu____10357 = FStar_Syntax_Subst.compress a2  in
                      uu____10357.FStar_Syntax_Syntax.n  in
                    (match uu____10356 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____10364) ->
                         let uu____10391 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____10391 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____10430 -> failwith "impossible"  in
                              let uu____10435 = patterns q1  in
                              (match uu____10435 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____10486 -> FStar_Pervasives_Native.None)
                | uu____10487 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____10508 = destruct_sq_forall phi  in
          (match uu____10508 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____10522 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____10528 = destruct_sq_exists phi  in
          (match uu____10528 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____10542 -> f1)
      | uu____10545 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____10549 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____10549
      (fun uu____10554  ->
         let uu____10555 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____10555
           (fun uu____10560  ->
              let uu____10561 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____10561
                (fun uu____10566  ->
                   let uu____10567 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____10567
                     (fun uu____10572  ->
                        let uu____10573 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____10573
                          (fun uu____10577  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____10589 =
      let uu____10590 = FStar_Syntax_Subst.compress t  in
      uu____10590.FStar_Syntax_Syntax.n  in
    match uu____10589 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____10597) ->
        let uu____10624 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____10624 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____10650 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____10650
             then
               let uu____10653 =
                 let uu____10662 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____10662]  in
               mk_app t uu____10653
             else e1)
    | uu____10682 ->
        let uu____10683 =
          let uu____10692 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____10692]  in
        mk_app t uu____10683
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____10727 =
            let uu____10732 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____10732  in
          let uu____10733 =
            let uu____10734 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____10734  in
          let uu____10737 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____10727 a.FStar_Syntax_Syntax.action_univs uu____10733
            FStar_Parser_Const.effect_Tot_lid uu____10737 [] pos
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
    let uu____10760 =
      let uu____10767 =
        let uu____10768 =
          let uu____10783 =
            let uu____10792 = FStar_Syntax_Syntax.as_arg t  in [uu____10792]
             in
          (reify_, uu____10783)  in
        FStar_Syntax_Syntax.Tm_app uu____10768  in
      FStar_Syntax_Syntax.mk uu____10767  in
    uu____10760 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10830 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____10854 = unfold_lazy i  in delta_qualifier uu____10854
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____10856 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____10857 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____10858 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____10881 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____10894 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____10895 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____10902 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____10903 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____10917) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____10922;
           FStar_Syntax_Syntax.index = uu____10923;
           FStar_Syntax_Syntax.sort = t2;_},uu____10925)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____10933) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____10939,uu____10940) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____10982) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____11003,t2,uu____11005) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____11026,t2) -> delta_qualifier t2
  
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
    let uu____11057 = delta_qualifier t  in incr_delta_depth uu____11057
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11063 =
      let uu____11064 = FStar_Syntax_Subst.compress t  in
      uu____11064.FStar_Syntax_Syntax.n  in
    match uu____11063 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____11067 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____11081 =
      let uu____11096 = unmeta e  in head_and_args uu____11096  in
    match uu____11081 with
    | (head1,args) ->
        let uu____11123 =
          let uu____11136 =
            let uu____11137 = un_uinst head1  in
            uu____11137.FStar_Syntax_Syntax.n  in
          (uu____11136, args)  in
        (match uu____11123 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11153) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____11173::(hd1,uu____11175)::(tl1,uu____11177)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____11224 =
               let uu____11227 =
                 let uu____11230 = list_elements tl1  in
                 FStar_Util.must uu____11230  in
               hd1 :: uu____11227  in
             FStar_Pervasives_Native.Some uu____11224
         | uu____11239 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____11260 .
    ('Auu____11260 -> 'Auu____11260) ->
      'Auu____11260 Prims.list -> 'Auu____11260 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____11285 = f a  in [uu____11285]
      | x::xs -> let uu____11290 = apply_last f xs  in x :: uu____11290
  
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
          let uu____11336 =
            let uu____11343 =
              let uu____11344 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____11344  in
            FStar_Syntax_Syntax.mk uu____11343  in
          uu____11336 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____11361 =
            let uu____11366 =
              let uu____11367 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____11367
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____11366 args  in
          uu____11361 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____11383 =
            let uu____11388 =
              let uu____11389 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____11389
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____11388 args  in
          uu____11383 FStar_Pervasives_Native.None pos  in
        let uu____11392 =
          let uu____11393 =
            let uu____11394 = FStar_Syntax_Syntax.iarg typ  in [uu____11394]
             in
          nil uu____11393 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____11422 =
                 let uu____11423 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____11430 =
                   let uu____11439 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____11446 =
                     let uu____11455 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____11455]  in
                   uu____11439 :: uu____11446  in
                 uu____11423 :: uu____11430  in
               cons1 uu____11422 t.FStar_Syntax_Syntax.pos) l uu____11392
  
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
        | uu____11549 -> false
  
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
          | uu____11656 -> false
  
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
        | uu____11811 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____11845 = FStar_ST.op_Bang debug_term_eq  in
          if uu____11845
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
        let t11 = let uu____12033 = unmeta_safe t1  in canon_app uu____12033
           in
        let t21 = let uu____12039 = unmeta_safe t2  in canon_app uu____12039
           in
        let uu____12042 =
          let uu____12047 =
            let uu____12048 =
              let uu____12051 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____12051  in
            uu____12048.FStar_Syntax_Syntax.n  in
          let uu____12052 =
            let uu____12053 =
              let uu____12056 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____12056  in
            uu____12053.FStar_Syntax_Syntax.n  in
          (uu____12047, uu____12052)  in
        match uu____12042 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____12057,uu____12058) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12065,FStar_Syntax_Syntax.Tm_uinst uu____12066) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____12073,uu____12074) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12097,FStar_Syntax_Syntax.Tm_delayed uu____12098) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____12121,uu____12122) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12149,FStar_Syntax_Syntax.Tm_ascribed uu____12150) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____12183 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____12183
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____12186 = FStar_Const.eq_const c1 c2  in
            check "const" uu____12186
        | (FStar_Syntax_Syntax.Tm_type
           uu____12187,FStar_Syntax_Syntax.Tm_type uu____12188) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____12237 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____12237) &&
              (let uu____12243 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____12243)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____12282 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____12282) &&
              (let uu____12288 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____12288)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____12302 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____12302)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____12349 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____12349) &&
              (let uu____12351 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____12351)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____12436 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____12436) &&
              (let uu____12438 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____12438)
        | (FStar_Syntax_Syntax.Tm_lazy uu____12453,uu____12454) ->
            let uu____12455 =
              let uu____12456 = unlazy t11  in
              term_eq_dbg dbg uu____12456 t21  in
            check "lazy_l" uu____12455
        | (uu____12457,FStar_Syntax_Syntax.Tm_lazy uu____12458) ->
            let uu____12459 =
              let uu____12460 = unlazy t21  in
              term_eq_dbg dbg t11 uu____12460  in
            check "lazy_r" uu____12459
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____12496 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____12496))
              &&
              (let uu____12498 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____12498)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____12500),FStar_Syntax_Syntax.Tm_uvar (u2,uu____12502)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (check "tm_quoted qi" (qi1 = qi2)) &&
              (let uu____12558 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____12558)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____12585 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____12585) &&
                   (let uu____12587 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____12587)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____12604 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____12604) &&
                    (let uu____12606 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____12606))
                   &&
                   (let uu____12608 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____12608)
             | uu____12609 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____12614) -> fail "unk"
        | (uu____12615,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____12616,uu____12617) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____12618,uu____12619) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____12620,uu____12621) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____12622,uu____12623) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____12624,uu____12625) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____12626,uu____12627) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____12644,uu____12645) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____12658,uu____12659) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____12666,uu____12667) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____12682,uu____12683) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____12706,uu____12707) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____12720,uu____12721) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____12734,uu____12735) ->
            fail "bottom"
        | (uu____12742,FStar_Syntax_Syntax.Tm_bvar uu____12743) ->
            fail "bottom"
        | (uu____12744,FStar_Syntax_Syntax.Tm_name uu____12745) ->
            fail "bottom"
        | (uu____12746,FStar_Syntax_Syntax.Tm_fvar uu____12747) ->
            fail "bottom"
        | (uu____12748,FStar_Syntax_Syntax.Tm_constant uu____12749) ->
            fail "bottom"
        | (uu____12750,FStar_Syntax_Syntax.Tm_type uu____12751) ->
            fail "bottom"
        | (uu____12752,FStar_Syntax_Syntax.Tm_abs uu____12753) ->
            fail "bottom"
        | (uu____12770,FStar_Syntax_Syntax.Tm_arrow uu____12771) ->
            fail "bottom"
        | (uu____12784,FStar_Syntax_Syntax.Tm_refine uu____12785) ->
            fail "bottom"
        | (uu____12792,FStar_Syntax_Syntax.Tm_app uu____12793) ->
            fail "bottom"
        | (uu____12808,FStar_Syntax_Syntax.Tm_match uu____12809) ->
            fail "bottom"
        | (uu____12832,FStar_Syntax_Syntax.Tm_let uu____12833) ->
            fail "bottom"
        | (uu____12846,FStar_Syntax_Syntax.Tm_uvar uu____12847) ->
            fail "bottom"
        | (uu____12860,FStar_Syntax_Syntax.Tm_meta uu____12861) ->
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
               let uu____12888 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____12888)
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
               let uu____12909 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____12909)
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
        ((let uu____12929 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____12929) &&
           (let uu____12931 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____12931))
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
    fun uu____12936  ->
      fun uu____12937  ->
        match (uu____12936, uu____12937) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____13062 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____13062) &&
               (let uu____13064 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____13064))
              &&
              (let uu____13066 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____13105 -> false  in
               check "branch when" uu____13066)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____13123 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____13123) &&
           (let uu____13129 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____13129))
          &&
          (let uu____13131 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____13131)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____13143 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____13143 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13196 ->
        let uu____13219 =
          let uu____13220 = FStar_Syntax_Subst.compress t  in
          sizeof uu____13220  in
        (Prims.parse_int "1") + uu____13219
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____13222 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____13222
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____13224 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____13224
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____13231 = sizeof t1  in (FStar_List.length us) + uu____13231
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____13234) ->
        let uu____13255 = sizeof t1  in
        let uu____13256 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____13267  ->
                 match uu____13267 with
                 | (bv,uu____13273) ->
                     let uu____13274 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____13274) (Prims.parse_int "0") bs
           in
        uu____13255 + uu____13256
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____13297 = sizeof hd1  in
        let uu____13298 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____13309  ->
                 match uu____13309 with
                 | (arg,uu____13315) ->
                     let uu____13316 = sizeof arg  in acc + uu____13316)
            (Prims.parse_int "0") args
           in
        uu____13297 + uu____13298
    | uu____13317 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____13328 =
        let uu____13329 = un_uinst t  in uu____13329.FStar_Syntax_Syntax.n
         in
      match uu____13328 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____13333 -> false
  
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
        let uu____13374 = FStar_Options.set_options t s  in
        match uu____13374 with
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
          ((let uu____13382 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____13382 (fun a236  -> ()));
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
    | FStar_Syntax_Syntax.Tm_delayed uu____13408 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____13434 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____13449 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____13450 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____13451 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____13460) ->
        let uu____13481 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____13481 with
         | (bs1,t2) ->
             let uu____13490 =
               FStar_List.collect
                 (fun uu____13500  ->
                    match uu____13500 with
                    | (b,uu____13508) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____13509 = unbound_variables t2  in
             FStar_List.append uu____13490 uu____13509)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____13530 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____13530 with
         | (bs1,c1) ->
             let uu____13539 =
               FStar_List.collect
                 (fun uu____13549  ->
                    match uu____13549 with
                    | (b,uu____13557) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____13558 = unbound_variables_comp c1  in
             FStar_List.append uu____13539 uu____13558)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____13567 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____13567 with
         | (bs,t2) ->
             let uu____13584 =
               FStar_List.collect
                 (fun uu____13594  ->
                    match uu____13594 with
                    | (b1,uu____13602) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____13603 = unbound_variables t2  in
             FStar_List.append uu____13584 uu____13603)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____13628 =
          FStar_List.collect
            (fun uu____13640  ->
               match uu____13640 with
               | (x,uu____13650) -> unbound_variables x) args
           in
        let uu____13655 = unbound_variables t1  in
        FStar_List.append uu____13628 uu____13655
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____13696 = unbound_variables t1  in
        let uu____13699 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____13714 = FStar_Syntax_Subst.open_branch br  in
                  match uu____13714 with
                  | (p,wopt,t2) ->
                      let uu____13736 = unbound_variables t2  in
                      let uu____13739 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____13736 uu____13739))
           in
        FStar_List.append uu____13696 uu____13699
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____13753) ->
        let uu____13794 = unbound_variables t1  in
        let uu____13797 =
          let uu____13800 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____13831 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____13800 uu____13831  in
        FStar_List.append uu____13794 uu____13797
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____13869 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____13872 =
          let uu____13875 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____13878 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____13883 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____13885 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____13885 with
                 | (uu____13900,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____13875 uu____13878  in
        FStar_List.append uu____13869 uu____13872
    | FStar_Syntax_Syntax.Tm_let ((uu____13902,lbs),t1) ->
        let uu____13919 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____13919 with
         | (lbs1,t2) ->
             let uu____13934 = unbound_variables t2  in
             let uu____13937 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____13944 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____13947 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____13944 uu____13947) lbs1
                in
             FStar_List.append uu____13934 uu____13937)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____13964 = unbound_variables t1  in
        let uu____13967 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____14000  ->
                      match uu____14000 with
                      | (a,uu____14010) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____14015,uu____14016,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____14022,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____14028 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____14035 -> []
          | FStar_Syntax_Syntax.Meta_named uu____14036 -> []  in
        FStar_List.append uu____13964 uu____13967

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____14043) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____14053) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____14063 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____14066 =
          FStar_List.collect
            (fun uu____14078  ->
               match uu____14078 with
               | (a,uu____14088) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____14063 uu____14066
