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
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____186 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____186
            then []
            else (let uu____202 = arg_of_non_null_binder b  in [uu____202])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  =
  fun binders  ->
    let uu____236 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____318 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____318
              then
                let b1 =
                  let uu____342 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____342, (FStar_Pervasives_Native.snd b))  in
                let uu____349 = arg_of_non_null_binder b1  in (b1, uu____349)
              else
                (let uu____371 = arg_of_non_null_binder b  in (b, uu____371))))
       in
    FStar_All.pipe_right uu____236 FStar_List.unzip
  
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
              let uu____503 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____503
              then
                let uu____510 = b  in
                match uu____510 with
                | (a,imp) ->
                    let b1 =
                      let uu____530 =
                        let uu____531 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____531  in
                      FStar_Ident.id_of_text uu____530  in
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
        let uu____571 =
          let uu____578 =
            let uu____579 =
              let uu____594 = name_binders binders  in (uu____594, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____579  in
          FStar_Syntax_Syntax.mk uu____578  in
        uu____571 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____616 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____652  ->
            match uu____652 with
            | (t,imp) ->
                let uu____663 =
                  let uu____664 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____664
                   in
                (uu____663, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____718  ->
            match uu____718 with
            | (t,imp) ->
                let uu____735 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____735, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____747 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____747
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____758 . 'Auu____758 -> 'Auu____758 Prims.list =
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
          (fun uu____878  ->
             fun uu____879  ->
               match (uu____878, uu____879) with
               | ((x,uu____905),(y,uu____907)) ->
                   let uu____928 =
                     let uu____935 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____935)  in
                   FStar_Syntax_Syntax.NT uu____928) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____948) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____954,uu____955) -> unmeta e2
    | uu____996 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____1009 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____1016 -> e1
         | uu____1025 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1027,uu____1028) ->
        unmeta_safe e2
    | uu____1069 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____1083 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____1084 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1094 = univ_kernel u1  in
        (match uu____1094 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____1105 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____1112 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____1122 = univ_kernel u  in FStar_Pervasives_Native.snd uu____1122
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____1137,uu____1138) ->
          failwith "Impossible: compare_univs"
      | (uu____1139,FStar_Syntax_Syntax.U_bvar uu____1140) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____1141) ->
          ~- (Prims.parse_int "1")
      | (uu____1142,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____1143) -> ~- (Prims.parse_int "1")
      | (uu____1144,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____1147,FStar_Syntax_Syntax.U_unif
         uu____1148) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____1157,FStar_Syntax_Syntax.U_name
         uu____1158) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____1185 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____1186 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____1185 - uu____1186
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____1217 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____1217
                 (fun uu____1232  ->
                    match uu____1232 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1246,uu____1247) ->
          ~- (Prims.parse_int "1")
      | (uu____1250,FStar_Syntax_Syntax.U_max uu____1251) ->
          (Prims.parse_int "1")
      | uu____1254 ->
          let uu____1259 = univ_kernel u1  in
          (match uu____1259 with
           | (k1,n1) ->
               let uu____1266 = univ_kernel u2  in
               (match uu____1266 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1285 = compare_univs u1 u2  in
      uu____1285 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1300 =
        let uu____1301 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1301;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1300
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1320 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1329 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1351 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1360 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1386 =
          let uu____1387 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1387  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1386;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1416 =
          let uu____1417 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1417  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1416;
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
      let uu___118_1452 = c  in
      let uu____1453 =
        let uu____1454 =
          let uu___119_1455 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___119_1455.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___119_1455.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___119_1455.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___119_1455.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1454  in
      {
        FStar_Syntax_Syntax.n = uu____1453;
        FStar_Syntax_Syntax.pos = (uu___118_1452.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___118_1452.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1480 -> c
        | FStar_Syntax_Syntax.GTotal uu____1489 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___120_1500 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___120_1500.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___120_1500.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___120_1500.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___120_1500.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___121_1501 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___121_1501.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___121_1501.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1504  ->
           let uu____1505 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1505)
  
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
    | uu____1544 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1555 -> true
    | FStar_Syntax_Syntax.GTotal uu____1564 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___106_1585  ->
               match uu___106_1585 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1586 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___107_1595  ->
               match uu___107_1595 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1596 -> false)))
  
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
            (fun uu___108_1605  ->
               match uu___108_1605 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1606 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___109_1619  ->
            match uu___109_1619 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1620 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___110_1629  ->
            match uu___110_1629 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1630 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1654 -> true
    | FStar_Syntax_Syntax.GTotal uu____1663 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___111_1676  ->
                   match uu___111_1676 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1677 -> false)))
  
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
            (fun uu___112_1710  ->
               match uu___112_1710 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1711 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1722 =
      let uu____1723 = FStar_Syntax_Subst.compress t  in
      uu____1723.FStar_Syntax_Syntax.n  in
    match uu____1722 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1726,c) -> is_pure_or_ghost_comp c
    | uu____1748 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1759 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1765 =
      let uu____1766 = FStar_Syntax_Subst.compress t  in
      uu____1766.FStar_Syntax_Syntax.n  in
    match uu____1765 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1769,c) -> is_lemma_comp c
    | uu____1791 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1797 =
      let uu____1798 = FStar_Syntax_Subst.compress t  in
      uu____1798.FStar_Syntax_Syntax.n  in
    match uu____1797 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1802) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____1828) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____1865,t1,uu____1867) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1893,uu____1894) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1936) -> head_of t1
    | uu____1941 -> t
  
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
    | uu____2018 -> (t1, [])
  
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
        let uu____2099 = head_and_args' head1  in
        (match uu____2099 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____2168 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2194) ->
        FStar_Syntax_Subst.compress t2
    | uu____2199 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2205 =
      let uu____2206 = FStar_Syntax_Subst.compress t  in
      uu____2206.FStar_Syntax_Syntax.n  in
    match uu____2205 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____2209,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____2235)::uu____2236 ->
                  let pats' = unmeta pats  in
                  let uu____2296 = head_and_args pats'  in
                  (match uu____2296 with
                   | (head1,uu____2314) ->
                       let uu____2339 =
                         let uu____2340 = un_uinst head1  in
                         uu____2340.FStar_Syntax_Syntax.n  in
                       (match uu____2339 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____2344 -> false))
              | uu____2345 -> false)
         | uu____2356 -> false)
    | uu____2357 -> false
  
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
                (fun uu___113_2371  ->
                   match uu___113_2371 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2372 -> false)))
    | uu____2373 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2388) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2398) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2426 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2435 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___122_2447 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___122_2447.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___122_2447.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___122_2447.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___122_2447.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2460  ->
           let uu____2461 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____2461 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___114_2476  ->
            match uu___114_2476 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2477 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2483 -> []
    | FStar_Syntax_Syntax.GTotal uu____2500 -> []
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
    | uu____2537 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2545,uu____2546) ->
        unascribe e2
    | uu____2587 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2639,uu____2640) ->
          ascribe t' k
      | uu____2681 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2707 =
      let uu____2716 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2716  in
    uu____2707 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2775 =
      let uu____2776 = FStar_Syntax_Subst.compress t  in
      uu____2776.FStar_Syntax_Syntax.n  in
    match uu____2775 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2780 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2780
    | uu____2781 -> t
  
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
      | uu____2792 -> false
  
let rec unlazy_as_t :
  'Auu____2803 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2803
  =
  fun k  ->
    fun t  ->
      let uu____2814 =
        let uu____2815 = FStar_Syntax_Subst.compress t  in
        uu____2815.FStar_Syntax_Syntax.n  in
      match uu____2814 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2820;
            FStar_Syntax_Syntax.rng = uu____2821;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____2824 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2863 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2863;
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
    let uu____2875 =
      let uu____2890 = unascribe t  in head_and_args' uu____2890  in
    match uu____2875 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2920 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2926 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2932 -> false
  
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
      let equal_if uu___115_3056 = if uu___115_3056 then Equal else Unknown
         in
      let equal_iff uu___116_3063 = if uu___116_3063 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____3081 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____3093) -> NotEqual
        | (uu____3094,NotEqual ) -> NotEqual
        | (Unknown ,uu____3095) -> Unknown
        | (uu____3096,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____3118 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3118
        then
          let uu____3120 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3197  ->
                    match uu____3197 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3238 = eq_tm a1 a2  in
                        eq_inj acc uu____3238) Equal) uu____3120
        else NotEqual  in
      let uu____3240 =
        let uu____3245 =
          let uu____3246 = unmeta t11  in uu____3246.FStar_Syntax_Syntax.n
           in
        let uu____3249 =
          let uu____3250 = unmeta t21  in uu____3250.FStar_Syntax_Syntax.n
           in
        (uu____3245, uu____3249)  in
      match uu____3240 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3255,uu____3256) ->
          let uu____3257 = unlazy t11  in eq_tm uu____3257 t21
      | (uu____3258,FStar_Syntax_Syntax.Tm_lazy uu____3259) ->
          let uu____3260 = unlazy t21  in eq_tm t11 uu____3260
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
            (let uu____3286 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____3286)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3299 = eq_tm f g  in
          eq_and uu____3299
            (fun uu____3302  ->
               let uu____3303 = eq_univs_list us vs  in equal_if uu____3303)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3304),uu____3305) -> Unknown
      | (uu____3306,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3307)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3310 = FStar_Const.eq_const c d  in equal_iff uu____3310
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3312)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3314))) ->
          let uu____3343 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3343
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3396 =
            let uu____3401 =
              let uu____3402 = un_uinst h1  in
              uu____3402.FStar_Syntax_Syntax.n  in
            let uu____3405 =
              let uu____3406 = un_uinst h2  in
              uu____3406.FStar_Syntax_Syntax.n  in
            (uu____3401, uu____3405)  in
          (match uu____3396 with
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
                 (let uu____3418 =
                    let uu____3419 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3419  in
                  FStar_List.mem uu____3418 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3420 ->
               let uu____3425 = eq_tm h1 h2  in
               eq_and uu____3425 (fun uu____3427  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3532 = FStar_List.zip bs1 bs2  in
            let uu____3595 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3632  ->
                 fun a  ->
                   match uu____3632 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3725  -> branch_matches b1 b2))
              uu____3532 uu____3595
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3729 = eq_univs u v1  in equal_if uu____3729
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____3742 = eq_quoteinfo q1 q2  in
          eq_and uu____3742 (fun uu____3744  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____3757 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____3757 (fun uu____3759  -> eq_tm phi1 phi2)
      | uu____3760 -> Unknown

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
      | ([],uu____3846) -> NotEqual
      | (uu____3885,[]) -> NotEqual
      | ((x1,b1,t1)::a11,(x2,b2,t2)::a21) ->
          if
            Prims.op_Negation
              ((FStar_Syntax_Syntax.bv_eq x1 x2) && (b1 = b2))
          then NotEqual
          else
            (let uu____3997 = eq_tm t1 t2  in
             match uu____3997 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____3998 = eq_antiquotes a11 a21  in
                 (match uu____3998 with
                  | NotEqual  -> NotEqual
                  | uu____3999 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____4014) -> NotEqual
      | (uu____4021,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | uu____4044 -> NotEqual

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
        | (uu____4131,uu____4132) -> false  in
      let uu____4141 = b1  in
      match uu____4141 with
      | (p1,w1,t1) ->
          let uu____4175 = b2  in
          (match uu____4175 with
           | (p2,w2,t2) ->
               let uu____4209 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4209
               then
                 let uu____4210 =
                   (let uu____4213 = eq_tm t1 t2  in uu____4213 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4222 = eq_tm t11 t21  in
                             uu____4222 = Equal) w1 w2)
                    in
                 (if uu____4210 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4284)::a11,(b,uu____4287)::b1) ->
          let uu____4361 = eq_tm a b  in
          (match uu____4361 with
           | Equal  -> eq_args a11 b1
           | uu____4362 -> Unknown)
      | uu____4363 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4397) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4403,uu____4404) ->
        unrefine t2
    | uu____4445 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4451 =
      let uu____4452 = FStar_Syntax_Subst.compress t  in
      uu____4452.FStar_Syntax_Syntax.n  in
    match uu____4451 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4455 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4469) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4474 ->
        let uu____4491 =
          let uu____4492 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4492 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4491 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4554,uu____4555) ->
        is_uvar t1
    | uu____4596 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4602 =
      let uu____4603 = unrefine t  in uu____4603.FStar_Syntax_Syntax.n  in
    match uu____4602 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4608) -> is_unit t1
    | uu____4613 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4619 =
      let uu____4620 = unrefine t  in uu____4620.FStar_Syntax_Syntax.n  in
    match uu____4619 with
    | FStar_Syntax_Syntax.Tm_type uu____4623 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____4626) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4652) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____4657,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____4679 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____4685 =
      let uu____4686 = FStar_Syntax_Subst.compress e  in
      uu____4686.FStar_Syntax_Syntax.n  in
    match uu____4685 with
    | FStar_Syntax_Syntax.Tm_abs uu____4689 -> true
    | uu____4708 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4714 =
      let uu____4715 = FStar_Syntax_Subst.compress t  in
      uu____4715.FStar_Syntax_Syntax.n  in
    match uu____4714 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4718 -> true
    | uu____4733 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4741) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4747,uu____4748) ->
        pre_typ t2
    | uu____4789 -> t1
  
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
      let uu____4813 =
        let uu____4814 = un_uinst typ1  in uu____4814.FStar_Syntax_Syntax.n
         in
      match uu____4813 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____4879 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____4909 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____4929,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____4936) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____4941,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____4952,uu____4953,uu____4954,uu____4955,uu____4956) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____4966,uu____4967,uu____4968,uu____4969) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____4975,uu____4976,uu____4977,uu____4978,uu____4979) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____4985,uu____4986) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4988,uu____4989) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____4992 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____4993 -> []
    | FStar_Syntax_Syntax.Sig_main uu____4994 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5007 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___117_5030  ->
    match uu___117_5030 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5043 'Auu____5044 .
    ('Auu____5043 FStar_Syntax_Syntax.syntax,'Auu____5044)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____5055  ->
    match uu____5055 with | (hd1,uu____5063) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5076 'Auu____5077 .
    ('Auu____5076 FStar_Syntax_Syntax.syntax,'Auu____5077)
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
      | uu____5174 ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args))
            FStar_Pervasives_Native.None r
  
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
          let uu____5246 = FStar_Ident.range_of_lid l  in
          let uu____5247 =
            let uu____5256 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5256  in
          uu____5247 FStar_Pervasives_Native.None uu____5246
      | uu____5264 ->
          let e =
            let uu____5278 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5278 args  in
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
      let uu____5293 =
        let uu____5298 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____5298, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____5293
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
          let uu____5349 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5349
          then
            let uu____5350 =
              let uu____5355 =
                let uu____5356 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____5356  in
              let uu____5357 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5355, uu____5357)  in
            FStar_Ident.mk_ident uu____5350
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___123_5360 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___123_5360.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___123_5360.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5361 = mk_field_projector_name_from_ident lid nm  in
        (uu____5361, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5372) -> ses
    | uu____5381 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____5390 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5401 = FStar_Syntax_Unionfind.find uv  in
      match uu____5401 with
      | FStar_Pervasives_Native.Some uu____5404 ->
          let uu____5405 =
            let uu____5406 =
              let uu____5407 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5407  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5406  in
          failwith uu____5405
      | uu____5408 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____5483 -> q1 = q2
  
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
              let uu____5528 =
                let uu___124_5529 = rc  in
                let uu____5530 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___124_5529.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____5530;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___124_5529.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____5528
           in
        match bs with
        | [] -> t
        | uu____5547 ->
            let body =
              let uu____5549 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____5549  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____5583 =
                   let uu____5590 =
                     let uu____5591 =
                       let uu____5610 =
                         let uu____5619 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____5619 bs'  in
                       let uu____5634 = close_lopt lopt'  in
                       (uu____5610, t1, uu____5634)  in
                     FStar_Syntax_Syntax.Tm_abs uu____5591  in
                   FStar_Syntax_Syntax.mk uu____5590  in
                 uu____5583 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____5652 ->
                 let uu____5659 =
                   let uu____5666 =
                     let uu____5667 =
                       let uu____5686 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____5695 = close_lopt lopt  in
                       (uu____5686, body, uu____5695)  in
                     FStar_Syntax_Syntax.Tm_abs uu____5667  in
                   FStar_Syntax_Syntax.mk uu____5666  in
                 uu____5659 FStar_Pervasives_Native.None
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
      | uu____5753 ->
          let uu____5762 =
            let uu____5769 =
              let uu____5770 =
                let uu____5785 = FStar_Syntax_Subst.close_binders bs  in
                let uu____5794 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____5785, uu____5794)  in
              FStar_Syntax_Syntax.Tm_arrow uu____5770  in
            FStar_Syntax_Syntax.mk uu____5769  in
          uu____5762 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
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
      let uu____5845 =
        let uu____5846 = FStar_Syntax_Subst.compress t  in
        uu____5846.FStar_Syntax_Syntax.n  in
      match uu____5845 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____5876) ->
               let uu____5885 =
                 let uu____5886 = FStar_Syntax_Subst.compress tres  in
                 uu____5886.FStar_Syntax_Syntax.n  in
               (match uu____5885 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____5929 -> t)
           | uu____5930 -> t)
      | uu____5931 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____5948 =
        let uu____5949 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____5949 t.FStar_Syntax_Syntax.pos  in
      let uu____5950 =
        let uu____5957 =
          let uu____5958 =
            let uu____5965 =
              let uu____5968 =
                let uu____5969 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____5969]  in
              FStar_Syntax_Subst.close uu____5968 t  in
            (b, uu____5965)  in
          FStar_Syntax_Syntax.Tm_refine uu____5958  in
        FStar_Syntax_Syntax.mk uu____5957  in
      uu____5950 FStar_Pervasives_Native.None uu____5948
  
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
        let uu____6050 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6050 with
         | (bs1,c1) ->
             let uu____6069 = is_total_comp c1  in
             if uu____6069
             then
               let uu____6082 = arrow_formals_comp (comp_result c1)  in
               (match uu____6082 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6148;
           FStar_Syntax_Syntax.index = uu____6149;
           FStar_Syntax_Syntax.sort = k2;_},uu____6151)
        -> arrow_formals_comp k2
    | uu____6158 ->
        let uu____6159 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6159)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                               FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____6193 = arrow_formals_comp k  in
    match uu____6193 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____6285 =
            let uu___125_6286 = rc  in
            let uu____6287 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___125_6286.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____6287;
              FStar_Syntax_Syntax.residual_flags =
                (uu___125_6286.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____6285
      | uu____6296 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____6330 =
        let uu____6331 =
          let uu____6334 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____6334  in
        uu____6331.FStar_Syntax_Syntax.n  in
      match uu____6330 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____6380 = aux t2 what  in
          (match uu____6380 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____6452 -> ([], t1, abs_body_lcomp)  in
    let uu____6469 = aux t FStar_Pervasives_Native.None  in
    match uu____6469 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____6517 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____6517 with
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
                    | (FStar_Pervasives_Native.None ,uu____6678) -> def
                    | (uu____6689,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____6701) ->
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
            let uu____6797 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____6797 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____6832 ->
            let t' = arrow binders c  in
            let uu____6844 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____6844 with
             | (uvs1,t'1) ->
                 let uu____6865 =
                   let uu____6866 = FStar_Syntax_Subst.compress t'1  in
                   uu____6866.FStar_Syntax_Syntax.n  in
                 (match uu____6865 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____6915 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____6936 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____6943 -> false
  
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
      let uu____6991 =
        let uu____6992 = pre_typ t  in uu____6992.FStar_Syntax_Syntax.n  in
      match uu____6991 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____6996 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____7007 =
        let uu____7008 = pre_typ t  in uu____7008.FStar_Syntax_Syntax.n  in
      match uu____7007 with
      | FStar_Syntax_Syntax.Tm_fvar uu____7011 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____7013) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____7039) ->
          is_constructed_typ t1 lid
      | uu____7044 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____7055 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____7056 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____7057 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____7059) -> get_tycon t2
    | uu____7084 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____7090 =
      let uu____7091 = un_uinst t  in uu____7091.FStar_Syntax_Syntax.n  in
    match uu____7090 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____7095 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____7102 =
        let uu____7105 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____7105  in
      match uu____7102 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____7118 -> false
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
  fun uu____7130  ->
    let u =
      let uu____7136 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_5  -> FStar_Syntax_Syntax.U_unif _0_5)
        uu____7136
       in
    let uu____7153 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____7153, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____7164 = eq_tm a a'  in
      match uu____7164 with | Equal  -> true | uu____7165 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____7168 =
    let uu____7175 =
      let uu____7176 =
        let uu____7177 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____7177
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____7176  in
    FStar_Syntax_Syntax.mk uu____7175  in
  uu____7168 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____7252 =
            let uu____7255 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____7256 =
              let uu____7263 =
                let uu____7264 =
                  let uu____7281 =
                    let uu____7292 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____7301 =
                      let uu____7312 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____7312]  in
                    uu____7292 :: uu____7301  in
                  (tand, uu____7281)  in
                FStar_Syntax_Syntax.Tm_app uu____7264  in
              FStar_Syntax_Syntax.mk uu____7263  in
            uu____7256 FStar_Pervasives_Native.None uu____7255  in
          FStar_Pervasives_Native.Some uu____7252
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____7391 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____7392 =
          let uu____7399 =
            let uu____7400 =
              let uu____7417 =
                let uu____7428 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____7437 =
                  let uu____7448 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____7448]  in
                uu____7428 :: uu____7437  in
              (op_t, uu____7417)  in
            FStar_Syntax_Syntax.Tm_app uu____7400  in
          FStar_Syntax_Syntax.mk uu____7399  in
        uu____7392 FStar_Pervasives_Native.None uu____7391
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____7507 =
      let uu____7514 =
        let uu____7515 =
          let uu____7532 =
            let uu____7543 = FStar_Syntax_Syntax.as_arg phi  in [uu____7543]
             in
          (t_not, uu____7532)  in
        FStar_Syntax_Syntax.Tm_app uu____7515  in
      FStar_Syntax_Syntax.mk uu____7514  in
    uu____7507 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____7736 =
      let uu____7743 =
        let uu____7744 =
          let uu____7761 =
            let uu____7772 = FStar_Syntax_Syntax.as_arg e  in [uu____7772]
             in
          (b2t_v, uu____7761)  in
        FStar_Syntax_Syntax.Tm_app uu____7744  in
      FStar_Syntax_Syntax.mk uu____7743  in
    uu____7736 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____7817 =
      let uu____7818 = unmeta t  in uu____7818.FStar_Syntax_Syntax.n  in
    match uu____7817 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____7822 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____7843 = is_t_true t1  in
      if uu____7843
      then t2
      else
        (let uu____7847 = is_t_true t2  in
         if uu____7847 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____7871 = is_t_true t1  in
      if uu____7871
      then t_true
      else
        (let uu____7875 = is_t_true t2  in
         if uu____7875 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____7899 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____7900 =
        let uu____7907 =
          let uu____7908 =
            let uu____7925 =
              let uu____7936 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____7945 =
                let uu____7956 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____7956]  in
              uu____7936 :: uu____7945  in
            (teq, uu____7925)  in
          FStar_Syntax_Syntax.Tm_app uu____7908  in
        FStar_Syntax_Syntax.mk uu____7907  in
      uu____7900 FStar_Pervasives_Native.None uu____7899
  
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
          let uu____8025 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____8026 =
            let uu____8033 =
              let uu____8034 =
                let uu____8051 =
                  let uu____8062 = FStar_Syntax_Syntax.iarg t  in
                  let uu____8071 =
                    let uu____8082 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____8091 =
                      let uu____8102 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____8102]  in
                    uu____8082 :: uu____8091  in
                  uu____8062 :: uu____8071  in
                (eq_inst, uu____8051)  in
              FStar_Syntax_Syntax.Tm_app uu____8034  in
            FStar_Syntax_Syntax.mk uu____8033  in
          uu____8026 FStar_Pervasives_Native.None uu____8025
  
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
        let uu____8181 =
          let uu____8188 =
            let uu____8189 =
              let uu____8206 =
                let uu____8217 = FStar_Syntax_Syntax.iarg t  in
                let uu____8226 =
                  let uu____8237 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____8246 =
                    let uu____8257 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____8257]  in
                  uu____8237 :: uu____8246  in
                uu____8217 :: uu____8226  in
              (t_has_type1, uu____8206)  in
            FStar_Syntax_Syntax.Tm_app uu____8189  in
          FStar_Syntax_Syntax.mk uu____8188  in
        uu____8181 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____8336 =
          let uu____8343 =
            let uu____8344 =
              let uu____8361 =
                let uu____8372 = FStar_Syntax_Syntax.iarg t  in
                let uu____8381 =
                  let uu____8392 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____8392]  in
                uu____8372 :: uu____8381  in
              (t_with_type1, uu____8361)  in
            FStar_Syntax_Syntax.Tm_app uu____8344  in
          FStar_Syntax_Syntax.mk uu____8343  in
        uu____8336 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____8440 =
    let uu____8447 =
      let uu____8448 =
        let uu____8455 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____8455, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____8448  in
    FStar_Syntax_Syntax.mk uu____8447  in
  uu____8440 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____8468 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____8481 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____8492 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____8468 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____8513  -> c0)
  
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
        let uu____8591 =
          let uu____8598 =
            let uu____8599 =
              let uu____8616 =
                let uu____8627 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____8636 =
                  let uu____8647 =
                    let uu____8656 =
                      let uu____8657 =
                        let uu____8658 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____8658]  in
                      abs uu____8657 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____8656  in
                  [uu____8647]  in
                uu____8627 :: uu____8636  in
              (fa, uu____8616)  in
            FStar_Syntax_Syntax.Tm_app uu____8599  in
          FStar_Syntax_Syntax.mk uu____8598  in
        uu____8591 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____8785 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____8785
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____8798 -> true
    | uu____8799 -> false
  
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
          let uu____8844 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____8844, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____8872 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____8872, FStar_Pervasives_Native.None, t2)  in
        let uu____8885 =
          let uu____8886 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____8886  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____8885
  
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
      let uu____8960 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____8963 =
        let uu____8974 = FStar_Syntax_Syntax.as_arg p  in [uu____8974]  in
      mk_app uu____8960 uu____8963
  
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
      let uu____9012 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____9015 =
        let uu____9026 = FStar_Syntax_Syntax.as_arg p  in [uu____9026]  in
      mk_app uu____9012 uu____9015
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____9060 = head_and_args t  in
    match uu____9060 with
    | (head1,args) ->
        let uu____9107 =
          let uu____9122 =
            let uu____9123 = un_uinst head1  in
            uu____9123.FStar_Syntax_Syntax.n  in
          (uu____9122, args)  in
        (match uu____9107 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____9142)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____9208 =
                    let uu____9213 =
                      let uu____9214 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____9214]  in
                    FStar_Syntax_Subst.open_term uu____9213 p  in
                  (match uu____9208 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____9271 -> failwith "impossible"  in
                       let uu____9278 =
                         let uu____9279 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____9279
                          in
                       if uu____9278
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____9293 -> FStar_Pervasives_Native.None)
         | uu____9296 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____9326 = head_and_args t  in
    match uu____9326 with
    | (head1,args) ->
        let uu____9377 =
          let uu____9392 =
            let uu____9393 = FStar_Syntax_Subst.compress head1  in
            uu____9393.FStar_Syntax_Syntax.n  in
          (uu____9392, args)  in
        (match uu____9377 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____9415;
               FStar_Syntax_Syntax.vars = uu____9416;_},u::[]),(t1,uu____9419)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____9466 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____9500 = head_and_args t  in
    match uu____9500 with
    | (head1,args) ->
        let uu____9551 =
          let uu____9566 =
            let uu____9567 = FStar_Syntax_Subst.compress head1  in
            uu____9567.FStar_Syntax_Syntax.n  in
          (uu____9566, args)  in
        (match uu____9551 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____9589;
               FStar_Syntax_Syntax.vars = uu____9590;_},u::[]),(t1,uu____9593)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____9640 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9666 = let uu____9683 = unmeta t  in head_and_args uu____9683
       in
    match uu____9666 with
    | (head1,uu____9685) ->
        let uu____9710 =
          let uu____9711 = un_uinst head1  in
          uu____9711.FStar_Syntax_Syntax.n  in
        (match uu____9710 with
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
         | uu____9715 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____9733 =
      let uu____9746 =
        let uu____9747 = FStar_Syntax_Subst.compress t  in
        uu____9747.FStar_Syntax_Syntax.n  in
      match uu____9746 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____9876 =
            let uu____9887 =
              let uu____9888 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____9888  in
            (b, uu____9887)  in
          FStar_Pervasives_Native.Some uu____9876
      | uu____9905 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____9733
      (fun uu____9943  ->
         match uu____9943 with
         | (b,c) ->
             let uu____9980 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____9980 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____10043 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____10076 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____10076
  
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
    match projectee with | QAll _0 -> true | uu____10124 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____10162 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____10198 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____10235) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____10247) ->
          unmeta_monadic t
      | uu____10260 -> f2  in
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
      let aux f2 uu____10344 =
        match uu____10344 with
        | (lid,arity) ->
            let uu____10353 =
              let uu____10370 = unmeta_monadic f2  in
              head_and_args uu____10370  in
            (match uu____10353 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____10400 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____10400
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____10477 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____10477)
      | uu____10490 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____10551 = head_and_args t1  in
        match uu____10551 with
        | (t2,args) ->
            let uu____10606 = un_uinst t2  in
            let uu____10607 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____10648  ->
                      match uu____10648 with
                      | (t3,imp) ->
                          let uu____10667 = unascribe t3  in
                          (uu____10667, imp)))
               in
            (uu____10606, uu____10607)
         in
      let rec aux qopt out t1 =
        let uu____10716 = let uu____10739 = flat t1  in (qopt, uu____10739)
           in
        match uu____10716 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____10778;
                 FStar_Syntax_Syntax.vars = uu____10779;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____10782);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____10783;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____10784;_},uu____10785)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____10884;
                 FStar_Syntax_Syntax.vars = uu____10885;_},uu____10886::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____10889);
                  FStar_Syntax_Syntax.pos = uu____10890;
                  FStar_Syntax_Syntax.vars = uu____10891;_},uu____10892)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____11006;
               FStar_Syntax_Syntax.vars = uu____11007;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____11010);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____11011;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____11012;_},uu____11013)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____11104 =
              let uu____11107 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____11107  in
            aux uu____11104 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____11115;
               FStar_Syntax_Syntax.vars = uu____11116;_},uu____11117::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____11120);
                FStar_Syntax_Syntax.pos = uu____11121;
                FStar_Syntax_Syntax.vars = uu____11122;_},uu____11123)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____11230 =
              let uu____11233 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____11233  in
            aux uu____11230 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____11241) ->
            let bs = FStar_List.rev out  in
            let uu____11291 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____11291 with
             | (bs1,t2) ->
                 let uu____11300 = patterns t2  in
                 (match uu____11300 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____11348 -> FStar_Pervasives_Native.None  in
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
      let uu____11424 = un_squash t  in
      FStar_Util.bind_opt uu____11424
        (fun t1  ->
           let uu____11440 = head_and_args' t1  in
           match uu____11440 with
           | (hd1,args) ->
               let uu____11479 =
                 let uu____11484 =
                   let uu____11485 = un_uinst hd1  in
                   uu____11485.FStar_Syntax_Syntax.n  in
                 (uu____11484, (FStar_List.length args))  in
               (match uu____11479 with
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
                | uu____11506 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____11535 = un_squash t  in
      FStar_Util.bind_opt uu____11535
        (fun t1  ->
           let uu____11550 = arrow_one t1  in
           match uu____11550 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____11565 =
                 let uu____11566 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____11566  in
               if uu____11565
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____11573 = comp_to_comp_typ_nouniv c  in
                    uu____11573.FStar_Syntax_Syntax.result_typ  in
                  let uu____11574 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____11574
                  then
                    let uu____11579 = patterns q  in
                    match uu____11579 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____11641 =
                       let uu____11642 =
                         let uu____11647 =
                           let uu____11648 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____11659 =
                             let uu____11670 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____11670]  in
                           uu____11648 :: uu____11659  in
                         (FStar_Parser_Const.imp_lid, uu____11647)  in
                       BaseConn uu____11642  in
                     FStar_Pervasives_Native.Some uu____11641))
           | uu____11703 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____11711 = un_squash t  in
      FStar_Util.bind_opt uu____11711
        (fun t1  ->
           let uu____11742 = head_and_args' t1  in
           match uu____11742 with
           | (hd1,args) ->
               let uu____11781 =
                 let uu____11796 =
                   let uu____11797 = un_uinst hd1  in
                   uu____11797.FStar_Syntax_Syntax.n  in
                 (uu____11796, args)  in
               (match uu____11781 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____11814)::(a2,uu____11816)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____11867 =
                      let uu____11868 = FStar_Syntax_Subst.compress a2  in
                      uu____11868.FStar_Syntax_Syntax.n  in
                    (match uu____11867 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____11875) ->
                         let uu____11910 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____11910 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____11963 -> failwith "impossible"  in
                              let uu____11970 = patterns q1  in
                              (match uu____11970 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____12031 -> FStar_Pervasives_Native.None)
                | uu____12032 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____12055 = destruct_sq_forall phi  in
          (match uu____12055 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____12071 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____12077 = destruct_sq_exists phi  in
          (match uu____12077 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____12093 -> f1)
      | uu____12096 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____12100 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____12100
      (fun uu____12105  ->
         let uu____12106 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____12106
           (fun uu____12111  ->
              let uu____12112 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____12112
                (fun uu____12117  ->
                   let uu____12118 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____12118
                     (fun uu____12123  ->
                        let uu____12124 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____12124
                          (fun uu____12128  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____12140 =
      let uu____12141 = FStar_Syntax_Subst.compress t  in
      uu____12141.FStar_Syntax_Syntax.n  in
    match uu____12140 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____12148) ->
        let uu____12183 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____12183 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____12217 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____12217
             then
               let uu____12222 =
                 let uu____12233 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____12233]  in
               mk_app t uu____12222
             else e1)
    | uu____12259 ->
        let uu____12260 =
          let uu____12271 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____12271]  in
        mk_app t uu____12260
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____12312 =
            let uu____12317 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____12317  in
          let uu____12318 =
            let uu____12319 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____12319  in
          let uu____12322 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____12312 a.FStar_Syntax_Syntax.action_univs uu____12318
            FStar_Parser_Const.effect_Tot_lid uu____12322 [] pos
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
    let uu____12345 =
      let uu____12352 =
        let uu____12353 =
          let uu____12370 =
            let uu____12381 = FStar_Syntax_Syntax.as_arg t  in [uu____12381]
             in
          (reify_, uu____12370)  in
        FStar_Syntax_Syntax.Tm_app uu____12353  in
      FStar_Syntax_Syntax.mk uu____12352  in
    uu____12345 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____12427 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____12451 = unfold_lazy i  in delta_qualifier uu____12451
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____12453 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____12454 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____12455 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____12478 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____12491 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____12492 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____12499 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____12500 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____12516) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____12521;
           FStar_Syntax_Syntax.index = uu____12522;
           FStar_Syntax_Syntax.sort = t2;_},uu____12524)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____12532) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____12538,uu____12539) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____12581) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____12606,t2,uu____12608) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____12633,t2) -> delta_qualifier t2
  
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
    let uu____12664 = delta_qualifier t  in incr_delta_depth uu____12664
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____12670 =
      let uu____12671 = FStar_Syntax_Subst.compress t  in
      uu____12671.FStar_Syntax_Syntax.n  in
    match uu____12670 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____12674 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____12688 =
      let uu____12705 = unmeta e  in head_and_args uu____12705  in
    match uu____12688 with
    | (head1,args) ->
        let uu____12736 =
          let uu____12751 =
            let uu____12752 = un_uinst head1  in
            uu____12752.FStar_Syntax_Syntax.n  in
          (uu____12751, args)  in
        (match uu____12736 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12770) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____12794::(hd1,uu____12796)::(tl1,uu____12798)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____12865 =
               let uu____12868 =
                 let uu____12871 = list_elements tl1  in
                 FStar_Util.must uu____12871  in
               hd1 :: uu____12868  in
             FStar_Pervasives_Native.Some uu____12865
         | uu____12880 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____12903 .
    ('Auu____12903 -> 'Auu____12903) ->
      'Auu____12903 Prims.list -> 'Auu____12903 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____12928 = f a  in [uu____12928]
      | x::xs -> let uu____12933 = apply_last f xs  in x :: uu____12933
  
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
          let uu____12979 =
            let uu____12986 =
              let uu____12987 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____12987  in
            FStar_Syntax_Syntax.mk uu____12986  in
          uu____12979 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____13004 =
            let uu____13009 =
              let uu____13010 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____13010
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____13009 args  in
          uu____13004 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____13026 =
            let uu____13031 =
              let uu____13032 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____13032
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____13031 args  in
          uu____13026 FStar_Pervasives_Native.None pos  in
        let uu____13035 =
          let uu____13036 =
            let uu____13037 = FStar_Syntax_Syntax.iarg typ  in [uu____13037]
             in
          nil uu____13036 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____13071 =
                 let uu____13072 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____13081 =
                   let uu____13092 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____13101 =
                     let uu____13112 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____13112]  in
                   uu____13092 :: uu____13101  in
                 uu____13072 :: uu____13081  in
               cons1 uu____13071 t.FStar_Syntax_Syntax.pos) l uu____13035
  
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
        | uu____13216 -> false
  
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
          | uu____13323 -> false
  
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
        | uu____13478 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____13512 = FStar_ST.op_Bang debug_term_eq  in
          if uu____13512
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
        let t11 = let uu____13708 = unmeta_safe t1  in canon_app uu____13708
           in
        let t21 = let uu____13714 = unmeta_safe t2  in canon_app uu____13714
           in
        let uu____13717 =
          let uu____13722 =
            let uu____13723 =
              let uu____13726 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____13726  in
            uu____13723.FStar_Syntax_Syntax.n  in
          let uu____13727 =
            let uu____13728 =
              let uu____13731 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____13731  in
            uu____13728.FStar_Syntax_Syntax.n  in
          (uu____13722, uu____13727)  in
        match uu____13717 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____13732,uu____13733) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____13740,FStar_Syntax_Syntax.Tm_uinst uu____13741) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____13748,uu____13749) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____13772,FStar_Syntax_Syntax.Tm_delayed uu____13773) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____13796,uu____13797) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____13824,FStar_Syntax_Syntax.Tm_ascribed uu____13825) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____13858 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____13858
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____13861 = FStar_Const.eq_const c1 c2  in
            check "const" uu____13861
        | (FStar_Syntax_Syntax.Tm_type
           uu____13862,FStar_Syntax_Syntax.Tm_type uu____13863) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____13920 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____13920) &&
              (let uu____13928 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____13928)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____13975 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____13975) &&
              (let uu____13983 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____13983)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____13997 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____13997)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____14052 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____14052) &&
              (let uu____14054 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____14054)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____14141 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____14141) &&
              (let uu____14143 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____14143)
        | (FStar_Syntax_Syntax.Tm_lazy uu____14158,uu____14159) ->
            let uu____14160 =
              let uu____14161 = unlazy t11  in
              term_eq_dbg dbg uu____14161 t21  in
            check "lazy_l" uu____14160
        | (uu____14162,FStar_Syntax_Syntax.Tm_lazy uu____14163) ->
            let uu____14164 =
              let uu____14165 = unlazy t21  in
              term_eq_dbg dbg t11 uu____14165  in
            check "lazy_r" uu____14164
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____14201 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____14201))
              &&
              (let uu____14203 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____14203)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____14205),FStar_Syntax_Syntax.Tm_uvar (u2,uu____14207)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____14264 =
               let uu____14265 = eq_quoteinfo qi1 qi2  in uu____14265 = Equal
                in
             check "tm_quoted qi" uu____14264) &&
              (let uu____14267 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____14267)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____14294 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____14294) &&
                   (let uu____14296 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____14296)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____14313 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____14313) &&
                    (let uu____14315 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____14315))
                   &&
                   (let uu____14317 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____14317)
             | uu____14318 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____14323) -> fail "unk"
        | (uu____14324,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____14325,uu____14326) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____14327,uu____14328) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____14329,uu____14330) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____14331,uu____14332) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____14333,uu____14334) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____14335,uu____14336) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____14355,uu____14356) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____14371,uu____14372) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____14379,uu____14380) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____14397,uu____14398) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____14421,uu____14422) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____14435,uu____14436) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____14449,uu____14450) ->
            fail "bottom"
        | (uu____14457,FStar_Syntax_Syntax.Tm_bvar uu____14458) ->
            fail "bottom"
        | (uu____14459,FStar_Syntax_Syntax.Tm_name uu____14460) ->
            fail "bottom"
        | (uu____14461,FStar_Syntax_Syntax.Tm_fvar uu____14462) ->
            fail "bottom"
        | (uu____14463,FStar_Syntax_Syntax.Tm_constant uu____14464) ->
            fail "bottom"
        | (uu____14465,FStar_Syntax_Syntax.Tm_type uu____14466) ->
            fail "bottom"
        | (uu____14467,FStar_Syntax_Syntax.Tm_abs uu____14468) ->
            fail "bottom"
        | (uu____14487,FStar_Syntax_Syntax.Tm_arrow uu____14488) ->
            fail "bottom"
        | (uu____14503,FStar_Syntax_Syntax.Tm_refine uu____14504) ->
            fail "bottom"
        | (uu____14511,FStar_Syntax_Syntax.Tm_app uu____14512) ->
            fail "bottom"
        | (uu____14529,FStar_Syntax_Syntax.Tm_match uu____14530) ->
            fail "bottom"
        | (uu____14553,FStar_Syntax_Syntax.Tm_let uu____14554) ->
            fail "bottom"
        | (uu____14567,FStar_Syntax_Syntax.Tm_uvar uu____14568) ->
            fail "bottom"
        | (uu____14581,FStar_Syntax_Syntax.Tm_meta uu____14582) ->
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
               let uu____14615 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____14615)
          (fun q1  ->
             fun q2  ->
               let uu____14625 =
                 let uu____14626 = eq_aqual q1 q2  in uu____14626 = Equal  in
               check "arg qual" uu____14625) a1 a2

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
               let uu____14649 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____14649)
          (fun q1  ->
             fun q2  ->
               let uu____14659 =
                 let uu____14660 = eq_aqual q1 q2  in uu____14660 = Equal  in
               check "binder qual" uu____14659) b1 b2

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
        ((let uu____14676 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____14676) &&
           (let uu____14678 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____14678))
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
    fun uu____14683  ->
      fun uu____14684  ->
        match (uu____14683, uu____14684) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____14809 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____14809) &&
               (let uu____14811 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____14811))
              &&
              (let uu____14813 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____14852 -> false  in
               check "branch when" uu____14813)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____14870 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____14870) &&
           (let uu____14876 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____14876))
          &&
          (let uu____14878 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____14878)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____14890 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____14890 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14943 ->
        let uu____14966 =
          let uu____14967 = FStar_Syntax_Subst.compress t  in
          sizeof uu____14967  in
        (Prims.parse_int "1") + uu____14966
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____14969 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____14969
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____14971 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____14971
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____14978 = sizeof t1  in (FStar_List.length us) + uu____14978
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____14981) ->
        let uu____15006 = sizeof t1  in
        let uu____15007 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____15020  ->
                 match uu____15020 with
                 | (bv,uu____15028) ->
                     let uu____15033 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____15033) (Prims.parse_int "0") bs
           in
        uu____15006 + uu____15007
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____15060 = sizeof hd1  in
        let uu____15061 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____15074  ->
                 match uu____15074 with
                 | (arg,uu____15082) ->
                     let uu____15087 = sizeof arg  in acc + uu____15087)
            (Prims.parse_int "0") args
           in
        uu____15060 + uu____15061
    | uu____15088 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____15099 =
        let uu____15100 = un_uinst t  in uu____15100.FStar_Syntax_Syntax.n
         in
      match uu____15099 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____15104 -> false
  
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
        let uu____15145 = FStar_Options.set_options t s  in
        match uu____15145 with
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
          ((let uu____15153 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____15153 (fun a235  -> ()));
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
    | FStar_Syntax_Syntax.Tm_delayed uu____15179 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____15205 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____15220 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____15221 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____15222 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____15231) ->
        let uu____15256 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____15256 with
         | (bs1,t2) ->
             let uu____15265 =
               FStar_List.collect
                 (fun uu____15277  ->
                    match uu____15277 with
                    | (b,uu____15287) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____15292 = unbound_variables t2  in
             FStar_List.append uu____15265 uu____15292)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____15317 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____15317 with
         | (bs1,c1) ->
             let uu____15326 =
               FStar_List.collect
                 (fun uu____15338  ->
                    match uu____15338 with
                    | (b,uu____15348) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____15353 = unbound_variables_comp c1  in
             FStar_List.append uu____15326 uu____15353)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____15362 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____15362 with
         | (bs,t2) ->
             let uu____15385 =
               FStar_List.collect
                 (fun uu____15397  ->
                    match uu____15397 with
                    | (b1,uu____15407) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____15412 = unbound_variables t2  in
             FStar_List.append uu____15385 uu____15412)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____15441 =
          FStar_List.collect
            (fun uu____15455  ->
               match uu____15455 with
               | (x,uu____15467) -> unbound_variables x) args
           in
        let uu____15476 = unbound_variables t1  in
        FStar_List.append uu____15441 uu____15476
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____15517 = unbound_variables t1  in
        let uu____15520 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____15535 = FStar_Syntax_Subst.open_branch br  in
                  match uu____15535 with
                  | (p,wopt,t2) ->
                      let uu____15557 = unbound_variables t2  in
                      let uu____15560 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____15557 uu____15560))
           in
        FStar_List.append uu____15517 uu____15520
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____15574) ->
        let uu____15615 = unbound_variables t1  in
        let uu____15618 =
          let uu____15621 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____15652 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____15621 uu____15652  in
        FStar_List.append uu____15615 uu____15618
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____15690 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____15693 =
          let uu____15696 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____15699 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____15704 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____15706 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____15706 with
                 | (uu____15727,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____15696 uu____15699  in
        FStar_List.append uu____15690 uu____15693
    | FStar_Syntax_Syntax.Tm_let ((uu____15729,lbs),t1) ->
        let uu____15746 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____15746 with
         | (lbs1,t2) ->
             let uu____15761 = unbound_variables t2  in
             let uu____15764 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____15771 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____15774 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____15771 uu____15774) lbs1
                in
             FStar_List.append uu____15761 uu____15764)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____15791 = unbound_variables t1  in
        let uu____15794 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____15833  ->
                      match uu____15833 with
                      | (a,uu____15845) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____15854,uu____15855,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____15861,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____15867 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____15874 -> []
          | FStar_Syntax_Syntax.Meta_named uu____15875 -> []  in
        FStar_List.append uu____15791 uu____15794

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____15882) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____15892) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____15902 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____15905 =
          FStar_List.collect
            (fun uu____15919  ->
               match uu____15919 with
               | (a,uu____15931) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____15902 uu____15905
