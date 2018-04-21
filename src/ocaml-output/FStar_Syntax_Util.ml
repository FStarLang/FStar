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
          let uu____415 =
            let uu____416 =
              let uu____429 = name_binders binders  in (uu____429, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____416  in
          FStar_Syntax_Syntax.mk uu____415  in
        uu____408 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____447 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____489  ->
            match uu____489 with
            | (t,imp) ->
                let uu____500 =
                  let uu____501 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____501
                   in
                (uu____500, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____553  ->
            match uu____553 with
            | (t,imp) ->
                let uu____570 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____570, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____582 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____582
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____593 . 'Auu____593 -> 'Auu____593 Prims.list =
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
          (fun uu____689  ->
             fun uu____690  ->
               match (uu____689, uu____690) with
               | ((x,uu____708),(y,uu____710)) ->
                   let uu____719 =
                     let uu____726 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____726)  in
                   FStar_Syntax_Syntax.NT uu____719) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____735) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____741,uu____742) -> unmeta e2
    | uu____783 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____796 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____803 -> e1
         | uu____812 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____814,uu____815) ->
        unmeta_safe e2
    | uu____856 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____870 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____871 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____881 = univ_kernel u1  in
        (match uu____881 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____892 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____899 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____909 = univ_kernel u  in FStar_Pervasives_Native.snd uu____909
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____924,uu____925) ->
          failwith "Impossible: compare_univs"
      | (uu____926,FStar_Syntax_Syntax.U_bvar uu____927) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____928) ->
          ~- (Prims.parse_int "1")
      | (uu____929,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____930) -> ~- (Prims.parse_int "1")
      | (uu____931,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____934,FStar_Syntax_Syntax.U_unif
         uu____935) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____944,FStar_Syntax_Syntax.U_name
         uu____945) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____972 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____973 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____972 - uu____973
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____1004 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____1004
                 (fun uu____1019  ->
                    match uu____1019 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1033,uu____1034) ->
          ~- (Prims.parse_int "1")
      | (uu____1037,FStar_Syntax_Syntax.U_max uu____1038) ->
          (Prims.parse_int "1")
      | uu____1041 ->
          let uu____1046 = univ_kernel u1  in
          (match uu____1046 with
           | (k1,n1) ->
               let uu____1053 = univ_kernel u2  in
               (match uu____1053 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1072 = compare_univs u1 u2  in
      uu____1072 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1087 =
        let uu____1088 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1088;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1087
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1105 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1114 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1136 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1145 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1171 =
          let uu____1172 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1172  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1171;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1199 =
          let uu____1200 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1200  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1199;
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
      let uu___52_1233 = c  in
      let uu____1234 =
        let uu____1235 =
          let uu___53_1236 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___53_1236.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___53_1236.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___53_1236.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___53_1236.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1235  in
      {
        FStar_Syntax_Syntax.n = uu____1234;
        FStar_Syntax_Syntax.pos = (uu___52_1233.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___52_1233.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1257 -> c
        | FStar_Syntax_Syntax.GTotal uu____1266 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___54_1277 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___54_1277.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___54_1277.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___54_1277.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___54_1277.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___55_1278 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___55_1278.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___55_1278.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1281  ->
           let uu____1282 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1282)
  
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
    | uu____1317 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1328 -> true
    | FStar_Syntax_Syntax.GTotal uu____1337 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___40_1358  ->
               match uu___40_1358 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1359 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___41_1368  ->
               match uu___41_1368 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1369 -> false)))
  
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
            (fun uu___42_1378  ->
               match uu___42_1378 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1379 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___43_1392  ->
            match uu___43_1392 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1393 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___44_1402  ->
            match uu___44_1402 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1403 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1427 -> true
    | FStar_Syntax_Syntax.GTotal uu____1436 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___45_1449  ->
                   match uu___45_1449 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1450 -> false)))
  
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
            (fun uu___46_1478  ->
               match uu___46_1478 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1479 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1490 =
      let uu____1491 = FStar_Syntax_Subst.compress t  in
      uu____1491.FStar_Syntax_Syntax.n  in
    match uu____1490 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1494,c) -> is_pure_or_ghost_comp c
    | uu____1512 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1523 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1529 =
      let uu____1530 = FStar_Syntax_Subst.compress t  in
      uu____1530.FStar_Syntax_Syntax.n  in
    match uu____1529 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1533,c) -> is_lemma_comp c
    | uu____1551 -> false
  
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
    | uu____1618 -> (t1, [])
  
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
        let uu____1685 = head_and_args' head1  in
        (match uu____1685 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1742 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1764) ->
        FStar_Syntax_Subst.compress t2
    | uu____1769 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1775 =
      let uu____1776 = FStar_Syntax_Subst.compress t  in
      uu____1776.FStar_Syntax_Syntax.n  in
    match uu____1775 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1779,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1801)::uu____1802 ->
                  let pats' = unmeta pats  in
                  let uu____1846 = head_and_args pats'  in
                  (match uu____1846 with
                   | (head1,uu____1862) ->
                       let uu____1883 =
                         let uu____1884 = un_uinst head1  in
                         uu____1884.FStar_Syntax_Syntax.n  in
                       (match uu____1883 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1888 -> false))
              | uu____1889 -> false)
         | uu____1898 -> false)
    | uu____1899 -> false
  
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
                (fun uu___47_1913  ->
                   match uu___47_1913 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1914 -> false)))
    | uu____1915 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1930) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1940) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____1964 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____1973 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___56_1985 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___56_1985.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___56_1985.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___56_1985.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___56_1985.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____1998  ->
           let uu____1999 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____1999 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___48_2014  ->
            match uu___48_2014 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2015 -> false))
  
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
    | uu____2035 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2043,uu____2044) ->
        unascribe e2
    | uu____2085 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2137,uu____2138) ->
          ascribe t' k
      | uu____2179 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2205 =
      let uu____2214 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2214  in
    uu____2205 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2273 =
      let uu____2274 = FStar_Syntax_Subst.compress t  in
      uu____2274.FStar_Syntax_Syntax.n  in
    match uu____2273 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2278 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2278
    | uu____2279 -> t
  
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
            let uu____2318 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2318;
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
    let uu____2326 =
      let uu____2339 = unascribe t  in head_and_args' uu____2339  in
    match uu____2326 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown [@@deriving show]
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2365 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2371 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2377 -> false
  
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
      let equal_if uu___49_2453 = if uu___49_2453 then Equal else Unknown  in
      let equal_iff uu___50_2460 = if uu___50_2460 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2478 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2490) -> NotEqual
        | (uu____2491,NotEqual ) -> NotEqual
        | (Unknown ,uu____2492) -> Unknown
        | (uu____2493,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____2539 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2539
        then
          let uu____2541 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2599  ->
                    match uu____2599 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2625 = eq_tm a1 a2  in
                        eq_inj acc uu____2625) Equal) uu____2541
        else NotEqual  in
      let uu____2627 =
        let uu____2632 =
          let uu____2633 = unmeta t11  in uu____2633.FStar_Syntax_Syntax.n
           in
        let uu____2636 =
          let uu____2637 = unmeta t21  in uu____2637.FStar_Syntax_Syntax.n
           in
        (uu____2632, uu____2636)  in
      match uu____2627 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2642,uu____2643) ->
          let uu____2644 = unlazy t11  in eq_tm uu____2644 t21
      | (uu____2645,FStar_Syntax_Syntax.Tm_lazy uu____2646) ->
          let uu____2647 = unlazy t21  in eq_tm t11 uu____2647
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
            (let uu____2665 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2665)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2678 = eq_tm f g  in
          eq_and uu____2678
            (fun uu____2681  ->
               let uu____2682 = eq_univs_list us vs  in equal_if uu____2682)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2683),uu____2684) -> Unknown
      | (uu____2685,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2686)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2689 = FStar_Const.eq_const c d  in equal_iff uu____2689
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2691),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2693)) ->
          let uu____2742 = FStar_Syntax_Unionfind.equiv u1 u2  in
          equal_if uu____2742
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2787 =
            let uu____2792 =
              let uu____2793 = un_uinst h1  in
              uu____2793.FStar_Syntax_Syntax.n  in
            let uu____2796 =
              let uu____2797 = un_uinst h2  in
              uu____2797.FStar_Syntax_Syntax.n  in
            (uu____2792, uu____2796)  in
          (match uu____2787 with
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
                 (let uu____2809 =
                    let uu____2810 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____2810  in
                  FStar_List.mem uu____2809 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____2811 ->
               let uu____2816 = eq_tm h1 h2  in
               eq_and uu____2816 (fun uu____2818  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____2923 = FStar_List.zip bs1 bs2  in
            let uu____2986 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3023  ->
                 fun a  ->
                   match uu____3023 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3116  -> branch_matches b1 b2))
              uu____2923 uu____2986
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3120 = eq_univs u v1  in equal_if uu____3120
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) -> if q1 = q2 then eq_tm t12 t22 else Unknown
      | uu____3134 -> Unknown

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
        | (uu____3217,uu____3218) -> false  in
      let uu____3227 = b1  in
      match uu____3227 with
      | (p1,w1,t1) ->
          let uu____3261 = b2  in
          (match uu____3261 with
           | (p2,w2,t2) ->
               let uu____3295 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3295
               then
                 let uu____3296 =
                   (let uu____3299 = eq_tm t1 t2  in uu____3299 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3308 = eq_tm t11 t21  in
                             uu____3308 = Equal) w1 w2)
                    in
                 (if uu____3296 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3342)::a11,(b,uu____3345)::b1) ->
          let uu____3399 = eq_tm a b  in
          (match uu____3399 with
           | Equal  -> eq_args a11 b1
           | uu____3400 -> Unknown)
      | uu____3401 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3415) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3421,uu____3422) ->
        unrefine t2
    | uu____3463 -> t1
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3469 =
      let uu____3470 = unrefine t  in uu____3470.FStar_Syntax_Syntax.n  in
    match uu____3469 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3475) -> is_unit t1
    | uu____3480 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3486 =
      let uu____3487 = unrefine t  in uu____3487.FStar_Syntax_Syntax.n  in
    match uu____3486 with
    | FStar_Syntax_Syntax.Tm_type uu____3490 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3493) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3515) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3520,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3538 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____3544 =
      let uu____3545 = FStar_Syntax_Subst.compress e  in
      uu____3545.FStar_Syntax_Syntax.n  in
    match uu____3544 with
    | FStar_Syntax_Syntax.Tm_abs uu____3548 -> true
    | uu____3565 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3571 =
      let uu____3572 = FStar_Syntax_Subst.compress t  in
      uu____3572.FStar_Syntax_Syntax.n  in
    match uu____3571 with
    | FStar_Syntax_Syntax.Tm_arrow uu____3575 -> true
    | uu____3588 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3596) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3602,uu____3603) ->
        pre_typ t2
    | uu____3644 -> t1
  
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
      let uu____3666 =
        let uu____3667 = un_uinst typ1  in uu____3667.FStar_Syntax_Syntax.n
         in
      match uu____3666 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____3722 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____3746 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____3764,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____3771) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____3776,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3787,uu____3788,uu____3789,uu____3790,uu____3791) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____3801,uu____3802,uu____3803,uu____3804) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____3810,uu____3811,uu____3812,uu____3813,uu____3814) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3820,uu____3821) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3823,uu____3824) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3827 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____3828 -> []
    | FStar_Syntax_Syntax.Sig_main uu____3829 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____3842 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___51_3865  ->
    match uu___51_3865 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____3878 'Auu____3879 .
    ('Auu____3878 FStar_Syntax_Syntax.syntax,'Auu____3879)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____3890  ->
    match uu____3890 with | (hd1,uu____3898) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____3911 'Auu____3912 .
    ('Auu____3911 FStar_Syntax_Syntax.syntax,'Auu____3912)
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
      | uu____4003 ->
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
          let uu____4059 = FStar_Ident.range_of_lid l  in
          let uu____4060 =
            let uu____4067 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____4067  in
          uu____4060 FStar_Pervasives_Native.None uu____4059
      | uu____4071 ->
          let e =
            let uu____4083 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____4083 args  in
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
      let uu____4098 =
        let uu____4103 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____4103, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____4098
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
          let uu____4154 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____4154
          then
            let uu____4155 =
              let uu____4160 =
                let uu____4161 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____4161  in
              let uu____4162 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____4160, uu____4162)  in
            FStar_Ident.mk_ident uu____4155
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___57_4165 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___57_4165.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___57_4165.FStar_Syntax_Syntax.sort)
          }  in
        let uu____4166 = mk_field_projector_name_from_ident lid nm  in
        (uu____4166, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4177) -> ses
    | uu____4186 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____4195 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____4206 = FStar_Syntax_Unionfind.find uv  in
      match uu____4206 with
      | FStar_Pervasives_Native.Some uu____4209 ->
          let uu____4210 =
            let uu____4211 =
              let uu____4212 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____4212  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4211  in
          failwith uu____4210
      | uu____4213 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____4288 -> q1 = q2
  
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
              let uu____4327 =
                let uu___58_4328 = rc  in
                let uu____4329 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___58_4328.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____4329;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___58_4328.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____4327
           in
        match bs with
        | [] -> t
        | uu____4340 ->
            let body =
              let uu____4342 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4342  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4370 =
                   let uu____4377 =
                     let uu____4378 =
                       let uu____4395 =
                         let uu____4402 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4402 bs'  in
                       let uu____4413 = close_lopt lopt'  in
                       (uu____4395, t1, uu____4413)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4378  in
                   FStar_Syntax_Syntax.mk uu____4377  in
                 uu____4370 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4429 ->
                 let uu____4436 =
                   let uu____4443 =
                     let uu____4444 =
                       let uu____4461 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4462 = close_lopt lopt  in
                       (uu____4461, body, uu____4462)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4444  in
                   FStar_Syntax_Syntax.mk uu____4443  in
                 uu____4436 FStar_Pervasives_Native.None
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
      | uu____4504 ->
          let uu____4511 =
            let uu____4518 =
              let uu____4519 =
                let uu____4532 = FStar_Syntax_Subst.close_binders bs  in
                let uu____4533 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____4532, uu____4533)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4519  in
            FStar_Syntax_Syntax.mk uu____4518  in
          uu____4511 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____4568 =
        let uu____4569 = FStar_Syntax_Subst.compress t  in
        uu____4569.FStar_Syntax_Syntax.n  in
      match uu____4568 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____4595) ->
               let uu____4604 =
                 let uu____4605 = FStar_Syntax_Subst.compress tres  in
                 uu____4605.FStar_Syntax_Syntax.n  in
               (match uu____4604 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____4640 -> t)
           | uu____4641 -> t)
      | uu____4642 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____4655 =
        let uu____4656 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____4656 t.FStar_Syntax_Syntax.pos  in
      let uu____4657 =
        let uu____4664 =
          let uu____4665 =
            let uu____4672 =
              let uu____4673 =
                let uu____4674 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____4674]  in
              FStar_Syntax_Subst.close uu____4673 t  in
            (b, uu____4672)  in
          FStar_Syntax_Syntax.Tm_refine uu____4665  in
        FStar_Syntax_Syntax.mk uu____4664  in
      uu____4657 FStar_Pervasives_Native.None uu____4655
  
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
        let uu____4727 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____4727 with
         | (bs1,c1) ->
             let uu____4744 = is_total_comp c1  in
             if uu____4744
             then
               let uu____4755 = arrow_formals_comp (comp_result c1)  in
               (match uu____4755 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____4801;
           FStar_Syntax_Syntax.index = uu____4802;
           FStar_Syntax_Syntax.sort = k2;_},uu____4804)
        -> arrow_formals_comp k2
    | uu____4811 ->
        let uu____4812 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4812)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____4840 = arrow_formals_comp k  in
    match uu____4840 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____4922 =
            let uu___59_4923 = rc  in
            let uu____4924 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___59_4923.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____4924;
              FStar_Syntax_Syntax.residual_flags =
                (uu___59_4923.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____4922
      | uu____4931 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____4963 =
        let uu____4964 =
          let uu____4967 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____4967  in
        uu____4964.FStar_Syntax_Syntax.n  in
      match uu____4963 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____5005 = aux t2 what  in
          (match uu____5005 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____5065 -> ([], t1, abs_body_lcomp)  in
    let uu____5078 = aux t FStar_Pervasives_Native.None  in
    match uu____5078 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____5120 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____5120 with
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
                    | (FStar_Pervasives_Native.None ,uu____5281) -> def
                    | (uu____5292,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____5304) ->
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
            let uu____5410 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____5410 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5439 ->
            let t' = arrow binders c  in
            let uu____5449 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5449 with
             | (uvs1,t'1) ->
                 let uu____5468 =
                   let uu____5469 = FStar_Syntax_Subst.compress t'1  in
                   uu____5469.FStar_Syntax_Syntax.n  in
                 (match uu____5468 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____5510 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____5529 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____5536 -> false
  
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
      let uu____5584 =
        let uu____5585 = pre_typ t  in uu____5585.FStar_Syntax_Syntax.n  in
      match uu____5584 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____5589 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____5600 =
        let uu____5601 = pre_typ t  in uu____5601.FStar_Syntax_Syntax.n  in
      match uu____5600 with
      | FStar_Syntax_Syntax.Tm_fvar uu____5604 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____5606) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5628) ->
          is_constructed_typ t1 lid
      | uu____5633 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____5644 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____5645 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____5646 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5648) -> get_tycon t2
    | uu____5669 -> FStar_Pervasives_Native.None
  
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
    let uu____5683 =
      let uu____5684 = un_uinst t  in uu____5684.FStar_Syntax_Syntax.n  in
    match uu____5683 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____5688 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____5695 =
        let uu____5698 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____5698  in
      match uu____5695 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____5711 -> false
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
  fun uu____5723  ->
    let u =
      let uu____5729 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_5  -> FStar_Syntax_Syntax.U_unif _0_5)
        uu____5729
       in
    let uu____5746 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____5746, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____5761 = eq_tm a a'  in
      match uu____5761 with | Equal  -> true | uu____5762 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____5765 =
    let uu____5772 =
      let uu____5773 =
        let uu____5774 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____5774
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____5773  in
    FStar_Syntax_Syntax.mk uu____5772  in
  uu____5765 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____5827 =
            let uu____5830 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____5831 =
              let uu____5838 =
                let uu____5839 =
                  let uu____5854 =
                    let uu____5857 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____5858 =
                      let uu____5861 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____5861]  in
                    uu____5857 :: uu____5858  in
                  (tand, uu____5854)  in
                FStar_Syntax_Syntax.Tm_app uu____5839  in
              FStar_Syntax_Syntax.mk uu____5838  in
            uu____5831 FStar_Pervasives_Native.None uu____5830  in
          FStar_Pervasives_Native.Some uu____5827
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____5890 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____5891 =
          let uu____5898 =
            let uu____5899 =
              let uu____5914 =
                let uu____5917 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____5918 =
                  let uu____5921 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____5921]  in
                uu____5917 :: uu____5918  in
              (op_t, uu____5914)  in
            FStar_Syntax_Syntax.Tm_app uu____5899  in
          FStar_Syntax_Syntax.mk uu____5898  in
        uu____5891 FStar_Pervasives_Native.None uu____5890
  
let (mk_neg :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____5936 =
      let uu____5943 =
        let uu____5944 =
          let uu____5959 =
            let uu____5962 = FStar_Syntax_Syntax.as_arg phi  in [uu____5962]
             in
          (t_not, uu____5959)  in
        FStar_Syntax_Syntax.Tm_app uu____5944  in
      FStar_Syntax_Syntax.mk uu____5943  in
    uu____5936 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____6045 =
      let uu____6052 =
        let uu____6053 =
          let uu____6068 =
            let uu____6071 = FStar_Syntax_Syntax.as_arg e  in [uu____6071]
             in
          (b2t_v, uu____6068)  in
        FStar_Syntax_Syntax.Tm_app uu____6053  in
      FStar_Syntax_Syntax.mk uu____6052  in
    uu____6045 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____6089 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____6090 =
        let uu____6097 =
          let uu____6098 =
            let uu____6113 =
              let uu____6116 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____6117 =
                let uu____6120 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____6120]  in
              uu____6116 :: uu____6117  in
            (teq, uu____6113)  in
          FStar_Syntax_Syntax.Tm_app uu____6098  in
        FStar_Syntax_Syntax.mk uu____6097  in
      uu____6090 FStar_Pervasives_Native.None uu____6089
  
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
          let uu____6147 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____6148 =
            let uu____6155 =
              let uu____6156 =
                let uu____6171 =
                  let uu____6174 = FStar_Syntax_Syntax.iarg t  in
                  let uu____6175 =
                    let uu____6178 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____6179 =
                      let uu____6182 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____6182]  in
                    uu____6178 :: uu____6179  in
                  uu____6174 :: uu____6175  in
                (eq_inst, uu____6171)  in
              FStar_Syntax_Syntax.Tm_app uu____6156  in
            FStar_Syntax_Syntax.mk uu____6155  in
          uu____6148 FStar_Pervasives_Native.None uu____6147
  
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
        let uu____6211 =
          let uu____6218 =
            let uu____6219 =
              let uu____6234 =
                let uu____6237 = FStar_Syntax_Syntax.iarg t  in
                let uu____6238 =
                  let uu____6241 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____6242 =
                    let uu____6245 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____6245]  in
                  uu____6241 :: uu____6242  in
                uu____6237 :: uu____6238  in
              (t_has_type1, uu____6234)  in
            FStar_Syntax_Syntax.Tm_app uu____6219  in
          FStar_Syntax_Syntax.mk uu____6218  in
        uu____6211 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____6276 =
          let uu____6283 =
            let uu____6284 =
              let uu____6299 =
                let uu____6302 = FStar_Syntax_Syntax.iarg t  in
                let uu____6303 =
                  let uu____6306 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____6306]  in
                uu____6302 :: uu____6303  in
              (t_with_type1, uu____6299)  in
            FStar_Syntax_Syntax.Tm_app uu____6284  in
          FStar_Syntax_Syntax.mk uu____6283  in
        uu____6276 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____6314 =
    let uu____6321 =
      let uu____6322 =
        let uu____6329 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____6329, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____6322  in
    FStar_Syntax_Syntax.mk uu____6321  in
  uu____6314 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____6344 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____6357 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____6368 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____6344 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____6389  -> c0)
  
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
        let uu____6463 =
          let uu____6470 =
            let uu____6471 =
              let uu____6486 =
                let uu____6489 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____6490 =
                  let uu____6493 =
                    let uu____6494 =
                      let uu____6495 =
                        let uu____6496 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____6496]  in
                      abs uu____6495 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____6494  in
                  [uu____6493]  in
                uu____6489 :: uu____6490  in
              (fa, uu____6486)  in
            FStar_Syntax_Syntax.Tm_app uu____6471  in
          FStar_Syntax_Syntax.mk uu____6470  in
        uu____6463 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____6549 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____6549
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____6560 -> true
    | uu____6561 -> false
  
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
          let uu____6606 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____6606, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____6634 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____6634, FStar_Pervasives_Native.None, t2)  in
        let uu____6647 =
          let uu____6648 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____6648  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____6647
  
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
      let uu____6722 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6725 =
        let uu____6734 = FStar_Syntax_Syntax.as_arg p  in [uu____6734]  in
      mk_app uu____6722 uu____6725
  
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
      let uu____6748 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6751 =
        let uu____6760 = FStar_Syntax_Syntax.as_arg p  in [uu____6760]  in
      mk_app uu____6748 uu____6751
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6770 = head_and_args t  in
    match uu____6770 with
    | (head1,args) ->
        let uu____6811 =
          let uu____6824 =
            let uu____6825 = un_uinst head1  in
            uu____6825.FStar_Syntax_Syntax.n  in
          (uu____6824, args)  in
        (match uu____6811 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____6842)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____6894 =
                    let uu____6899 =
                      let uu____6900 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____6900]  in
                    FStar_Syntax_Subst.open_term uu____6899 p  in
                  (match uu____6894 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____6929 -> failwith "impossible"  in
                       let uu____6934 =
                         let uu____6935 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____6935
                          in
                       if uu____6934
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____6945 -> FStar_Pervasives_Native.None)
         | uu____6948 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6976 = head_and_args t  in
    match uu____6976 with
    | (head1,args) ->
        let uu____7021 =
          let uu____7034 =
            let uu____7035 = FStar_Syntax_Subst.compress head1  in
            uu____7035.FStar_Syntax_Syntax.n  in
          (uu____7034, args)  in
        (match uu____7021 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____7055;
               FStar_Syntax_Syntax.vars = uu____7056;_},u::[]),(t1,uu____7059)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____7098 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7130 = head_and_args t  in
    match uu____7130 with
    | (head1,args) ->
        let uu____7175 =
          let uu____7188 =
            let uu____7189 = FStar_Syntax_Subst.compress head1  in
            uu____7189.FStar_Syntax_Syntax.n  in
          (uu____7188, args)  in
        (match uu____7175 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____7209;
               FStar_Syntax_Syntax.vars = uu____7210;_},u::[]),(t1,uu____7213)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____7252 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____7276 = let uu____7291 = unmeta t  in head_and_args uu____7291
       in
    match uu____7276 with
    | (head1,uu____7293) ->
        let uu____7314 =
          let uu____7315 = un_uinst head1  in
          uu____7315.FStar_Syntax_Syntax.n  in
        (match uu____7314 with
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
         | uu____7319 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7337 =
      let uu____7350 =
        let uu____7351 = FStar_Syntax_Subst.compress t  in
        uu____7351.FStar_Syntax_Syntax.n  in
      match uu____7350 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____7460 =
            let uu____7469 =
              let uu____7470 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____7470  in
            (b, uu____7469)  in
          FStar_Pervasives_Native.Some uu____7460
      | uu____7483 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____7337
      (fun uu____7519  ->
         match uu____7519 with
         | (b,c) ->
             let uu____7554 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____7554 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____7601 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____7628 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____7628
  
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
    match projectee with | QAll _0 -> true | uu____7676 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____7714 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____7750 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____7787) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____7799) ->
          unmeta_monadic t
      | uu____7812 -> f2  in
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
      let aux f2 uu____7896 =
        match uu____7896 with
        | (lid,arity) ->
            let uu____7905 =
              let uu____7920 = unmeta_monadic f2  in head_and_args uu____7920
               in
            (match uu____7905 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____7946 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____7946
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____8023 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____8023)
      | uu____8034 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____8089 = head_and_args t1  in
        match uu____8089 with
        | (t2,args) ->
            let uu____8136 = un_uinst t2  in
            let uu____8137 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____8170  ->
                      match uu____8170 with
                      | (t3,imp) ->
                          let uu____8181 = unascribe t3  in (uu____8181, imp)))
               in
            (uu____8136, uu____8137)
         in
      let rec aux qopt out t1 =
        let uu____8222 = let uu____8239 = flat t1  in (qopt, uu____8239)  in
        match uu____8222 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____8266;
                 FStar_Syntax_Syntax.vars = uu____8267;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____8270);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____8271;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____8272;_},uu____8273)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____8350;
                 FStar_Syntax_Syntax.vars = uu____8351;_},uu____8352::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____8355);
                  FStar_Syntax_Syntax.pos = uu____8356;
                  FStar_Syntax_Syntax.vars = uu____8357;_},uu____8358)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____8446;
               FStar_Syntax_Syntax.vars = uu____8447;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____8450);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8451;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8452;_},uu____8453)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____8524 =
              let uu____8527 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____8527  in
            aux uu____8524 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____8533;
               FStar_Syntax_Syntax.vars = uu____8534;_},uu____8535::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____8538);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____8539;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____8540;_},uu____8541)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____8624 =
              let uu____8627 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____8627  in
            aux uu____8624 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____8633) ->
            let bs = FStar_List.rev out  in
            let uu____8667 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____8667 with
             | (bs1,t2) ->
                 let uu____8676 = patterns t2  in
                 (match uu____8676 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____8738 -> FStar_Pervasives_Native.None  in
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
      let uu____8806 = un_squash t  in
      FStar_Util.bind_opt uu____8806
        (fun t1  ->
           let uu____8822 = head_and_args' t1  in
           match uu____8822 with
           | (hd1,args) ->
               let uu____8855 =
                 let uu____8860 =
                   let uu____8861 = un_uinst hd1  in
                   uu____8861.FStar_Syntax_Syntax.n  in
                 (uu____8860, (FStar_List.length args))  in
               (match uu____8855 with
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
                | uu____8944 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____8973 = un_squash t  in
      FStar_Util.bind_opt uu____8973
        (fun t1  ->
           let uu____8988 = arrow_one t1  in
           match uu____8988 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____9003 =
                 let uu____9004 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____9004  in
               if uu____9003
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____9011 = comp_to_comp_typ_nouniv c  in
                    uu____9011.FStar_Syntax_Syntax.result_typ  in
                  let uu____9012 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____9012
                  then
                    let uu____9015 = patterns q  in
                    match uu____9015 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____9071 =
                       let uu____9072 =
                         let uu____9077 =
                           let uu____9080 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____9081 =
                             let uu____9084 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____9084]  in
                           uu____9080 :: uu____9081  in
                         (FStar_Parser_Const.imp_lid, uu____9077)  in
                       BaseConn uu____9072  in
                     FStar_Pervasives_Native.Some uu____9071))
           | uu____9087 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____9095 = un_squash t  in
      FStar_Util.bind_opt uu____9095
        (fun t1  ->
           let uu____9126 = head_and_args' t1  in
           match uu____9126 with
           | (hd1,args) ->
               let uu____9159 =
                 let uu____9172 =
                   let uu____9173 = un_uinst hd1  in
                   uu____9173.FStar_Syntax_Syntax.n  in
                 (uu____9172, args)  in
               (match uu____9159 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____9188)::(a2,uu____9190)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____9225 =
                      let uu____9226 = FStar_Syntax_Subst.compress a2  in
                      uu____9226.FStar_Syntax_Syntax.n  in
                    (match uu____9225 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____9233) ->
                         let uu____9260 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____9260 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____9299 -> failwith "impossible"  in
                              let uu____9304 = patterns q1  in
                              (match uu____9304 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____9371 -> FStar_Pervasives_Native.None)
                | uu____9372 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____9393 = destruct_sq_forall phi  in
          (match uu____9393 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____9415 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____9421 = destruct_sq_exists phi  in
          (match uu____9421 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____9443 -> f1)
      | uu____9446 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____9450 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____9450
      (fun uu____9455  ->
         let uu____9456 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____9456
           (fun uu____9461  ->
              let uu____9462 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____9462
                (fun uu____9467  ->
                   let uu____9468 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____9468
                     (fun uu____9473  ->
                        let uu____9474 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____9474
                          (fun uu____9478  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____9486 =
      let uu____9487 = FStar_Syntax_Subst.compress t  in
      uu____9487.FStar_Syntax_Syntax.n  in
    match uu____9486 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____9494) ->
        let uu____9521 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____9521 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____9547 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____9547
             then
               let uu____9550 =
                 let uu____9559 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____9559]  in
               mk_app t uu____9550
             else e1)
    | uu____9561 ->
        let uu____9562 =
          let uu____9571 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____9571]  in
        mk_app t uu____9562
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____9588 =
            let uu____9593 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.Delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____9593  in
          let uu____9594 =
            let uu____9595 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____9595  in
          let uu____9598 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____9588 a.FStar_Syntax_Syntax.action_univs uu____9594
            FStar_Parser_Const.effect_Tot_lid uu____9598 [] pos
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
    let uu____9627 =
      let uu____9634 =
        let uu____9635 =
          let uu____9650 =
            let uu____9653 = FStar_Syntax_Syntax.as_arg t  in [uu____9653]
             in
          (reify_, uu____9650)  in
        FStar_Syntax_Syntax.Tm_app uu____9635  in
      FStar_Syntax_Syntax.mk uu____9634  in
    uu____9627 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____9667 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____9693 = unfold_lazy i  in delta_qualifier uu____9693
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____9695 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____9696 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____9697 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____9720 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____9737 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____9738 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____9745 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____9746 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____9760) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____9765;
           FStar_Syntax_Syntax.index = uu____9766;
           FStar_Syntax_Syntax.sort = t2;_},uu____9768)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____9776) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____9782,uu____9783) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____9825) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____9846,t2,uu____9848) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____9869,t2) -> delta_qualifier t2
  
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
    let uu____9899 = delta_qualifier t  in incr_delta_depth uu____9899
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9905 =
      let uu____9906 = FStar_Syntax_Subst.compress t  in
      uu____9906.FStar_Syntax_Syntax.n  in
    match uu____9905 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____9909 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9923 = let uu____9938 = unmeta e  in head_and_args uu____9938
       in
    match uu____9923 with
    | (head1,args) ->
        let uu____9965 =
          let uu____9978 =
            let uu____9979 = un_uinst head1  in
            uu____9979.FStar_Syntax_Syntax.n  in
          (uu____9978, args)  in
        (match uu____9965 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9995) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____10015::(hd1,uu____10017)::(tl1,uu____10019)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____10066 =
               let uu____10071 =
                 let uu____10076 = list_elements tl1  in
                 FStar_Util.must uu____10076  in
               hd1 :: uu____10071  in
             FStar_Pervasives_Native.Some uu____10066
         | uu____10089 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____10110 .
    ('Auu____10110 -> 'Auu____10110) ->
      'Auu____10110 Prims.list -> 'Auu____10110 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____10135 = f a  in [uu____10135]
      | x::xs -> let uu____10140 = apply_last f xs  in x :: uu____10140
  
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
          let uu____10186 =
            let uu____10193 =
              let uu____10194 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____10194  in
            FStar_Syntax_Syntax.mk uu____10193  in
          uu____10186 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____10211 =
            let uu____10216 =
              let uu____10217 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____10217
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____10216 args  in
          uu____10211 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____10233 =
            let uu____10238 =
              let uu____10239 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____10239
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____10238 args  in
          uu____10233 FStar_Pervasives_Native.None pos  in
        let uu____10242 =
          let uu____10243 =
            let uu____10244 = FStar_Syntax_Syntax.iarg typ  in [uu____10244]
             in
          nil uu____10243 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____10250 =
                 let uu____10251 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____10252 =
                   let uu____10255 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____10256 =
                     let uu____10259 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____10259]  in
                   uu____10255 :: uu____10256  in
                 uu____10251 :: uu____10252  in
               cons1 uu____10250 t.FStar_Syntax_Syntax.pos) l uu____10242
  
let (uvar_from_id :
  Prims.int ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun id1  ->
    fun t  ->
      let uu____10272 =
        let uu____10279 =
          let uu____10280 =
            let uu____10297 = FStar_Syntax_Unionfind.from_id id1  in
            (uu____10297, t)  in
          FStar_Syntax_Syntax.Tm_uvar uu____10280  in
        FStar_Syntax_Syntax.mk uu____10279  in
      uu____10272 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        | uu____10364 -> false
  
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
          | uu____10471 -> false
  
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
        | uu____10626 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____10660 = FStar_ST.op_Bang debug_term_eq  in
          if uu____10660
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
        let t11 = let uu____10848 = unmeta_safe t1  in canon_app uu____10848
           in
        let t21 = let uu____10852 = unmeta_safe t2  in canon_app uu____10852
           in
        let uu____10853 =
          let uu____10858 =
            let uu____10859 =
              let uu____10862 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____10862  in
            uu____10859.FStar_Syntax_Syntax.n  in
          let uu____10863 =
            let uu____10864 =
              let uu____10867 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____10867  in
            uu____10864.FStar_Syntax_Syntax.n  in
          (uu____10858, uu____10863)  in
        match uu____10853 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____10868,uu____10869) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10876,FStar_Syntax_Syntax.Tm_uinst uu____10877) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____10884,uu____10885) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10910,FStar_Syntax_Syntax.Tm_delayed uu____10911) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____10936,uu____10937) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10964,FStar_Syntax_Syntax.Tm_ascribed uu____10965) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____10998 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____10998
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____11001 = FStar_Const.eq_const c1 c2  in
            check "const" uu____11001
        | (FStar_Syntax_Syntax.Tm_type
           uu____11002,FStar_Syntax_Syntax.Tm_type uu____11003) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____11052 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____11052) &&
              (let uu____11058 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____11058)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____11097 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____11097) &&
              (let uu____11103 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____11103)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____11117 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____11117)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____11164 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____11164) &&
              (let uu____11166 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____11166)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____11251 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____11251) &&
              (let uu____11253 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____11253)
        | (FStar_Syntax_Syntax.Tm_lazy uu____11268,uu____11269) ->
            let uu____11270 =
              let uu____11271 = unlazy t11  in
              term_eq_dbg dbg uu____11271 t21  in
            check "lazy_l" uu____11270
        | (uu____11272,FStar_Syntax_Syntax.Tm_lazy uu____11273) ->
            let uu____11274 =
              let uu____11275 = unlazy t21  in
              term_eq_dbg dbg t11 uu____11275  in
            check "lazy_r" uu____11274
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____11311 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____11311))
              &&
              (let uu____11313 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____11313)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____11315),FStar_Syntax_Syntax.Tm_uvar (u2,uu____11317)) ->
            check "uvar" (u1 = u2)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (check "tm_quoted qi" (qi1 = qi2)) &&
              (let uu____11389 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____11389)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____11416 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____11416) &&
                   (let uu____11418 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____11418)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____11435 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____11435) &&
                    (let uu____11437 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____11437))
                   &&
                   (let uu____11439 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____11439)
             | uu____11440 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____11445) -> fail "unk"
        | (uu____11446,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____11447,uu____11448) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____11449,uu____11450) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____11451,uu____11452) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____11453,uu____11454) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____11455,uu____11456) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____11457,uu____11458) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____11475,uu____11476) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____11489,uu____11490) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____11497,uu____11498) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____11513,uu____11514) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____11537,uu____11538) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____11551,uu____11552) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____11569,uu____11570) ->
            fail "bottom"
        | (uu____11577,FStar_Syntax_Syntax.Tm_bvar uu____11578) ->
            fail "bottom"
        | (uu____11579,FStar_Syntax_Syntax.Tm_name uu____11580) ->
            fail "bottom"
        | (uu____11581,FStar_Syntax_Syntax.Tm_fvar uu____11582) ->
            fail "bottom"
        | (uu____11583,FStar_Syntax_Syntax.Tm_constant uu____11584) ->
            fail "bottom"
        | (uu____11585,FStar_Syntax_Syntax.Tm_type uu____11586) ->
            fail "bottom"
        | (uu____11587,FStar_Syntax_Syntax.Tm_abs uu____11588) ->
            fail "bottom"
        | (uu____11605,FStar_Syntax_Syntax.Tm_arrow uu____11606) ->
            fail "bottom"
        | (uu____11619,FStar_Syntax_Syntax.Tm_refine uu____11620) ->
            fail "bottom"
        | (uu____11627,FStar_Syntax_Syntax.Tm_app uu____11628) ->
            fail "bottom"
        | (uu____11643,FStar_Syntax_Syntax.Tm_match uu____11644) ->
            fail "bottom"
        | (uu____11667,FStar_Syntax_Syntax.Tm_let uu____11668) ->
            fail "bottom"
        | (uu____11681,FStar_Syntax_Syntax.Tm_uvar uu____11682) ->
            fail "bottom"
        | (uu____11699,FStar_Syntax_Syntax.Tm_meta uu____11700) ->
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
               let uu____11727 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____11727)
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
               let uu____11748 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____11748)
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
        ((let uu____11768 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____11768) &&
           (let uu____11770 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____11770))
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
    fun uu____11775  ->
      fun uu____11776  ->
        match (uu____11775, uu____11776) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____11901 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____11901) &&
               (let uu____11903 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____11903))
              &&
              (let uu____11905 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____11944 -> false  in
               check "branch when" uu____11905)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____11962 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____11962) &&
           (let uu____11968 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____11968))
          &&
          (let uu____11970 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____11970)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____11982 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____11982 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____12035 ->
        let uu____12060 =
          let uu____12061 = FStar_Syntax_Subst.compress t  in
          sizeof uu____12061  in
        (Prims.parse_int "1") + uu____12060
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____12063 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____12063
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____12065 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____12065
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____12072 = sizeof t1  in (FStar_List.length us) + uu____12072
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____12075) ->
        let uu____12096 = sizeof t1  in
        let uu____12097 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____12108  ->
                 match uu____12108 with
                 | (bv,uu____12114) ->
                     let uu____12115 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____12115) (Prims.parse_int "0") bs
           in
        uu____12096 + uu____12097
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____12138 = sizeof hd1  in
        let uu____12139 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____12150  ->
                 match uu____12150 with
                 | (arg,uu____12156) ->
                     let uu____12157 = sizeof arg  in acc + uu____12157)
            (Prims.parse_int "0") args
           in
        uu____12138 + uu____12139
    | uu____12158 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____12169 =
        let uu____12170 = un_uinst t  in uu____12170.FStar_Syntax_Syntax.n
         in
      match uu____12169 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____12174 -> false
  
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
        let uu____12215 = FStar_Options.set_options t s  in
        match uu____12215 with
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
          ((let uu____12223 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____12223 (fun a237  -> ()));
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
  
let rec (unbound_variables :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv Prims.list) =
  fun tm  ->
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____12243 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____12299 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____12300 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____12301 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____12310) ->
        let uu____12331 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____12331 with
         | (bs1,t2) ->
             let uu____12340 =
               FStar_List.collect
                 (fun uu____12350  ->
                    match uu____12350 with
                    | (b,uu____12358) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____12359 = unbound_variables t2  in
             FStar_List.append uu____12340 uu____12359)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____12380 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____12380 with
         | (bs1,c1) ->
             let uu____12389 =
               FStar_List.collect
                 (fun uu____12399  ->
                    match uu____12399 with
                    | (b,uu____12407) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____12408 = unbound_variables_comp c1  in
             FStar_List.append uu____12389 uu____12408)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____12417 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____12417 with
         | (bs,t2) ->
             let uu____12440 =
               FStar_List.collect
                 (fun uu____12450  ->
                    match uu____12450 with
                    | (b1,uu____12458) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____12459 = unbound_variables t2  in
             FStar_List.append uu____12440 uu____12459)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____12484 =
          FStar_List.collect
            (fun uu____12494  ->
               match uu____12494 with
               | (x,uu____12502) -> unbound_variables x) args
           in
        let uu____12503 = unbound_variables t1  in
        FStar_List.append uu____12484 uu____12503
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____12544 = unbound_variables t1  in
        let uu____12547 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____12576 = FStar_Syntax_Subst.open_branch br  in
                  match uu____12576 with
                  | (p,wopt,t2) ->
                      let uu____12598 = unbound_variables t2  in
                      let uu____12601 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____12598 uu____12601))
           in
        FStar_List.append uu____12544 uu____12547
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____12615) ->
        let uu____12656 = unbound_variables t1  in
        let uu____12659 =
          let uu____12662 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____12693 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____12662 uu____12693  in
        FStar_List.append uu____12656 uu____12659
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____12731 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____12734 =
          let uu____12737 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____12740 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____12745 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____12747 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____12747 with
                 | (uu____12768,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____12737 uu____12740  in
        FStar_List.append uu____12731 uu____12734
    | FStar_Syntax_Syntax.Tm_let ((uu____12770,lbs),t1) ->
        let uu____12787 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____12787 with
         | (lbs1,t2) ->
             let uu____12802 = unbound_variables t2  in
             let uu____12805 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____12812 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____12815 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____12812 uu____12815) lbs1
                in
             FStar_List.append uu____12802 uu____12805)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____12832 = unbound_variables t1  in
        let uu____12835 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____12864  ->
                      match uu____12864 with
                      | (a,uu____12872) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____12873,uu____12874,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____12880,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____12886 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____12893 -> []
          | FStar_Syntax_Syntax.Meta_named uu____12894 -> []  in
        FStar_List.append uu____12832 uu____12835

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.bv Prims.list) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____12899) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____12909) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____12919 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____12922 =
          FStar_List.collect
            (fun uu____12932  ->
               match uu____12932 with
               | (a,uu____12940) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____12919 uu____12922
