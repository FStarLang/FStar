open Prims
let tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let tts : FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let uu____32 = FStar_ST.op_Bang tts_f  in
    match uu____32 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun id1  ->
      let uu____91 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____91 id1.FStar_Ident.idRange
  
let mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident =
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
  
let is_name : FStar_Ident.lident -> Prims.bool =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.lift_native_int (0))
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
  
let args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____159 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____159
            then []
            else (let uu____171 = arg_of_non_null_binder b  in [uu____171])))
  
let args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2
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
  
let name_binders :
  FStar_Syntax_Syntax.binder Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
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
                        FStar_Syntax_Syntax.index =
                          (Prims.lift_native_int (0));
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      }  in
                    (b2, imp)
              else b))
  
let name_function_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
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
  
let null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders
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
  
let binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders
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
  
let binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list
  =
  fun fvs  ->
    let uu____582 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____582
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____593 . 'Auu____593 -> 'Auu____593 Prims.list =
  fun s  -> [s] 
let subst_of_list :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.subst_t
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
  
let rename_binders :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t
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
  
let rec unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____735) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____741,uu____742) -> unmeta e2
    | uu____783 -> e1
  
let rec unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
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
  
let rec univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.lift_native_int (0)))
    | FStar_Syntax_Syntax.U_name uu____870 ->
        (u, (Prims.lift_native_int (0)))
    | FStar_Syntax_Syntax.U_unif uu____871 ->
        (u, (Prims.lift_native_int (0)))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.lift_native_int (0)))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____881 = univ_kernel u1  in
        (match uu____881 with
         | (k,n1) -> (k, (n1 + (Prims.lift_native_int (1)))))
    | FStar_Syntax_Syntax.U_max uu____892 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____899 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  ->
    let uu____909 = univ_kernel u  in FStar_Pervasives_Native.snd uu____909
  
let rec compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____924,uu____925) ->
          failwith "Impossible: compare_univs"
      | (uu____926,FStar_Syntax_Syntax.U_bvar uu____927) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.lift_native_int (0))
      | (FStar_Syntax_Syntax.U_unknown ,uu____928) ->
          ~- (Prims.lift_native_int (1))
      | (uu____929,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.lift_native_int (1))
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.lift_native_int (0))
      | (FStar_Syntax_Syntax.U_zero ,uu____930) ->
          ~- (Prims.lift_native_int (1))
      | (uu____931,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.lift_native_int (1))
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____934,FStar_Syntax_Syntax.U_unif
         uu____935) -> ~- (Prims.lift_native_int (1))
      | (FStar_Syntax_Syntax.U_unif uu____944,FStar_Syntax_Syntax.U_name
         uu____945) -> (Prims.lift_native_int (1))
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
                        if c <> (Prims.lift_native_int (0))
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.lift_native_int (0))
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1033,uu____1034) ->
          ~- (Prims.lift_native_int (1))
      | (uu____1037,FStar_Syntax_Syntax.U_max uu____1038) ->
          (Prims.lift_native_int (1))
      | uu____1041 ->
          let uu____1046 = univ_kernel u1  in
          (match uu____1046 with
           | (k1,n1) ->
               let uu____1053 = univ_kernel u2  in
               (match uu____1053 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.lift_native_int (0)) then n1 - n2 else r))
  
let eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____1072 = compare_univs u1 u2  in
      uu____1072 = (Prims.lift_native_int (0))
  
let ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp
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
  
let comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1105 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1114 ->
        FStar_Parser_Const.effect_GTot_lid
  
let comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1136 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1145 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
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
  
let comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
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
  
let lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp
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
  
let comp_to_comp_typ :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
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
  
let is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1328 -> true
    | FStar_Syntax_Syntax.GTotal uu____1337 -> false
  
let is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
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
  
let is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
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
  
let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
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
  
let is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___43_1392  ->
            match uu___43_1392 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1393 -> false))
  
let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___44_1402  ->
            match uu___44_1402 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1403 -> false))
  
let is_tot_or_gtot_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    (is_total_comp c) ||
      (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid
         (comp_effect_name c))
  
let is_pure_effect : FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)
  
let is_pure_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
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
  
let is_ghost_effect : FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)
  
let is_div_effect : FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)
  
let is_pure_or_ghost_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  -> (is_pure_comp c) || (is_ghost_effect (comp_effect_name c)) 
let is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___46_1478  ->
               match uu___46_1478 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1479 -> false)))
  
let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1490 =
      let uu____1491 = FStar_Syntax_Subst.compress t  in
      uu____1491.FStar_Syntax_Syntax.n  in
    match uu____1490 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1494,c) -> is_pure_or_ghost_comp c
    | uu____1512 -> true
  
let is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1523 -> false
  
let is_lemma : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1529 =
      let uu____1530 = FStar_Syntax_Subst.compress t  in
      uu____1530.FStar_Syntax_Syntax.n  in
    match uu____1529 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1533,c) -> is_lemma_comp c
    | uu____1551 -> false
  
let head_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax,
                                                            FStar_Syntax_Syntax.aqual)
                                                            FStar_Pervasives_Native.tuple2
                                                            Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____1618 -> (t1, [])
  
let rec head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.term'
                                 FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1685 = head_and_args' head1  in
        (match uu____1685 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1742 -> (t1, [])
  
let un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1764) ->
        FStar_Syntax_Subst.compress t2
    | uu____1769 -> t1
  
let is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool =
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
  
let is_ml_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
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
  
let comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1930) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1940) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp
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
  
let is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___48_1998  ->
            match uu___48_1998 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____1999 -> false))
  
let primops : FStar_Ident.lident Prims.list =
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
let is_primop_lid : FStar_Ident.lident -> Prims.bool =
  fun l  ->
    FStar_All.pipe_right primops
      (FStar_Util.for_some (FStar_Ident.lid_equals l))
  
let is_primop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_primop_lid (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____2019 -> false
  
let rec unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2027,uu____2028) ->
        unascribe e2
    | uu____2069 -> e1
  
let rec ascribe :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.comp'
                                                             FStar_Syntax_Syntax.syntax)
       FStar_Util.either,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun k  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2121,uu____2122) ->
          ascribe t' k
      | uu____2163 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term =
  fun i  ->
    let uu____2189 =
      let uu____2198 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2198  in
    uu____2189 i.FStar_Syntax_Syntax.lkind i
  
let rec unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____2257 =
      let uu____2258 = FStar_Syntax_Subst.compress t  in
      uu____2258.FStar_Syntax_Syntax.n  in
    match uu____2257 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2262 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2262
    | uu____2263 -> t
  
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
            let uu____2302 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2302;
              FStar_Syntax_Syntax.lkind = k;
              FStar_Syntax_Syntax.typ = typ;
              FStar_Syntax_Syntax.rng = rng
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i)
            FStar_Pervasives_Native.None rng
  
let canon_app :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let uu____2310 =
      let uu____2323 = unascribe t  in head_and_args' uu____2323  in
    match uu____2310 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown [@@deriving show]
let uu___is_Equal : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2349 -> false
  
let uu___is_NotEqual : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2355 -> false
  
let uu___is_Unknown : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2361 -> false
  
let injectives : Prims.string Prims.list =
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
let rec eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___49_2437 = if uu___49_2437 then Equal else Unknown  in
      let equal_iff uu___50_2444 = if uu___50_2444 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2462 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2474) -> NotEqual
        | (uu____2475,NotEqual ) -> NotEqual
        | (Unknown ,uu____2476) -> Unknown
        | (uu____2477,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____2523 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2523
        then
          let uu____2525 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2583  ->
                    match uu____2583 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2609 = eq_tm a1 a2  in
                        eq_inj acc uu____2609) Equal) uu____2525
        else NotEqual  in
      let uu____2611 =
        let uu____2616 =
          let uu____2617 = unmeta t11  in uu____2617.FStar_Syntax_Syntax.n
           in
        let uu____2620 =
          let uu____2621 = unmeta t21  in uu____2621.FStar_Syntax_Syntax.n
           in
        (uu____2616, uu____2620)  in
      match uu____2611 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2626,uu____2627) ->
          let uu____2628 = unlazy t11  in eq_tm uu____2628 t21
      | (uu____2629,FStar_Syntax_Syntax.Tm_lazy uu____2630) ->
          let uu____2631 = unlazy t21  in eq_tm t11 uu____2631
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
            (let uu____2649 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2649)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2662 = eq_tm f g  in
          eq_and uu____2662
            (fun uu____2665  ->
               let uu____2666 = eq_univs_list us vs  in equal_if uu____2666)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2667),uu____2668) -> Unknown
      | (uu____2669,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2670)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2673 = FStar_Const.eq_const c d  in equal_iff uu____2673
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2675),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2677)) ->
          let uu____2726 = FStar_Syntax_Unionfind.equiv u1 u2  in
          equal_if uu____2726
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2771 =
            let uu____2776 =
              let uu____2777 = un_uinst h1  in
              uu____2777.FStar_Syntax_Syntax.n  in
            let uu____2780 =
              let uu____2781 = un_uinst h2  in
              uu____2781.FStar_Syntax_Syntax.n  in
            (uu____2776, uu____2780)  in
          (match uu____2771 with
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
                 (let uu____2793 =
                    let uu____2794 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____2794  in
                  FStar_List.mem uu____2793 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____2795 ->
               let uu____2800 = eq_tm h1 h2  in
               eq_and uu____2800 (fun uu____2802  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____2907 = FStar_List.zip bs1 bs2  in
            let uu____2970 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3007  ->
                 fun a  ->
                   match uu____3007 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3100  -> branch_matches b1 b2))
              uu____2907 uu____2970
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3104 = eq_univs u v1  in equal_if uu____3104
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) -> if q1 = q2 then eq_tm t12 t22 else Unknown
      | uu____3118 -> Unknown

and branch_matches :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax
                                                             FStar_Pervasives_Native.option,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                               FStar_Syntax_Syntax.syntax
                                                               FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 -> eq_result
  =
  fun b1  ->
    fun b2  ->
      let related_by f o1 o2 =
        match (o1, o2) with
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            true
        | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y) ->
            f x y
        | (uu____3201,uu____3202) -> false  in
      let uu____3211 = b1  in
      match uu____3211 with
      | (p1,w1,t1) ->
          let uu____3245 = b2  in
          (match uu____3245 with
           | (p2,w2,t2) ->
               let uu____3279 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3279
               then
                 let uu____3280 =
                   (let uu____3283 = eq_tm t1 t2  in uu____3283 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3292 = eq_tm t11 t21  in
                             uu____3292 = Equal) w1 w2)
                    in
                 (if uu____3280 then Equal else Unknown)
               else Unknown)

and eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3326)::a11,(b,uu____3329)::b1) ->
          let uu____3383 = eq_tm a b  in
          (match uu____3383 with
           | Equal  -> eq_args a11 b1
           | uu____3384 -> Unknown)
      | uu____3385 -> Unknown

and eq_univs_list :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool
  =
  fun us  ->
    fun vs  ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)

let rec unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3399) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3405,uu____3406) ->
        unrefine t2
    | uu____3447 -> t1
  
let rec is_unit : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3453 =
      let uu____3454 = unrefine t  in uu____3454.FStar_Syntax_Syntax.n  in
    match uu____3453 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3459) -> is_unit t1
    | uu____3464 -> false
  
let rec non_informative : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3470 =
      let uu____3471 = unrefine t  in uu____3471.FStar_Syntax_Syntax.n  in
    match uu____3470 with
    | FStar_Syntax_Syntax.Tm_type uu____3474 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3477) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3499) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3504,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3522 -> false
  
let is_fun : FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____3528 =
      let uu____3529 = FStar_Syntax_Subst.compress e  in
      uu____3529.FStar_Syntax_Syntax.n  in
    match uu____3528 with
    | FStar_Syntax_Syntax.Tm_abs uu____3532 -> true
    | uu____3549 -> false
  
let is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3555 =
      let uu____3556 = FStar_Syntax_Subst.compress t  in
      uu____3556.FStar_Syntax_Syntax.n  in
    match uu____3555 with
    | FStar_Syntax_Syntax.Tm_arrow uu____3559 -> true
    | uu____3572 -> false
  
let rec pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3580) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3586,uu____3587) ->
        pre_typ t2
    | uu____3628 -> t1
  
let destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ  in
      let uu____3650 =
        let uu____3651 = un_uinst typ1  in uu____3651.FStar_Syntax_Syntax.n
         in
      match uu____3650 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____3706 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____3730 -> FStar_Pervasives_Native.None
  
let lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____3748,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____3755) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____3760,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3771,uu____3772,uu____3773,uu____3774,uu____3775) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____3785,uu____3786,uu____3787,uu____3788) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____3794,uu____3795,uu____3796,uu____3797,uu____3798) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3804,uu____3805) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3807,uu____3808) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3811 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____3812 -> []
    | FStar_Syntax_Syntax.Sig_main uu____3813 -> []
  
let lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____3826 -> FStar_Pervasives_Native.None
  
let quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range
  =
  fun uu___51_3849  ->
    match uu___51_3849 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____3862 'Auu____3863 .
    ('Auu____3862 FStar_Syntax_Syntax.syntax,'Auu____3863)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____3874  ->
    match uu____3874 with | (hd1,uu____3882) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____3895 'Auu____3896 .
    ('Auu____3895 FStar_Syntax_Syntax.syntax,'Auu____3896)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range -> FStar_Range.range
  =
  fun args  ->
    fun r  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left
           (fun r1  -> fun a  -> FStar_Range.union_ranges r1 (range_of_arg a))
           r)
  
let mk_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____3987 ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args))
            FStar_Pervasives_Native.None r
  
let mk_data :
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term FStar_Syntax_Syntax.syntax
  =
  fun l  ->
    fun args  ->
      match args with
      | [] ->
          let uu____4043 = FStar_Ident.range_of_lid l  in
          let uu____4044 =
            let uu____4051 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____4051  in
          uu____4044 FStar_Pervasives_Native.None uu____4043
      | uu____4055 ->
          let e =
            let uu____4067 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____4067 args  in
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
  
let mangle_field_name : FStar_Ident.ident -> FStar_Ident.ident =
  fun x  ->
    FStar_Ident.mk_ident
      ((Prims.strcat "__fname__" x.FStar_Ident.idText),
        (x.FStar_Ident.idRange))
  
let unmangle_field_name : FStar_Ident.ident -> FStar_Ident.ident =
  fun x  ->
    if FStar_Util.starts_with x.FStar_Ident.idText "__fname__"
    then
      let uu____4082 =
        let uu____4087 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.lift_native_int (9))
           in
        (uu____4087, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____4082
    else x
  
let field_projector_prefix : Prims.string = "__proj__" 
let field_projector_sep : Prims.string = "__item__" 
let field_projector_contains_constructor : Prims.string -> Prims.bool =
  fun s  -> FStar_Util.starts_with s field_projector_prefix 
let mk_field_projector_name_from_string :
  Prims.string -> Prims.string -> Prims.string =
  fun constr  ->
    fun field  ->
      Prims.strcat field_projector_prefix
        (Prims.strcat constr (Prims.strcat field_projector_sep field))
  
let mk_field_projector_name_from_ident :
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
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
  
let mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv ->
      Prims.int ->
        (FStar_Ident.lident,FStar_Syntax_Syntax.bv)
          FStar_Pervasives_Native.tuple2
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____4138 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____4138
          then
            let uu____4139 =
              let uu____4144 =
                let uu____4145 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____4145  in
              let uu____4146 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____4144, uu____4146)  in
            FStar_Ident.mk_ident uu____4139
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___57_4149 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___57_4149.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___57_4149.FStar_Syntax_Syntax.sort)
          }  in
        let uu____4150 = mk_field_projector_name_from_ident lid nm  in
        (uu____4150, y)
  
let ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4161) -> ses
    | uu____4170 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____4179 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit =
  fun uv  ->
    fun t  ->
      let uu____4190 = FStar_Syntax_Unionfind.find uv  in
      match uu____4190 with
      | FStar_Pervasives_Native.Some uu____4193 ->
          let uu____4194 =
            let uu____4195 =
              let uu____4196 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____4196  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4195  in
          failwith uu____4194
      | uu____4197 -> FStar_Syntax_Unionfind.change uv t
  
let qualifier_equal :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Syntax_Syntax.qualifier -> Prims.bool
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
      | uu____4272 -> q1 = q2
  
let abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        let close_lopt lopt1 =
          match lopt1 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rc ->
              let uu____4311 =
                let uu___58_4312 = rc  in
                let uu____4313 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___58_4312.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____4313;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___58_4312.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____4311
           in
        match bs with
        | [] -> t
        | uu____4324 ->
            let body =
              let uu____4326 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4326  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4354 =
                   let uu____4361 =
                     let uu____4362 =
                       let uu____4379 =
                         let uu____4386 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4386 bs'  in
                       let uu____4397 = close_lopt lopt'  in
                       (uu____4379, t1, uu____4397)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4362  in
                   FStar_Syntax_Syntax.mk uu____4361  in
                 uu____4354 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4413 ->
                 let uu____4420 =
                   let uu____4427 =
                     let uu____4428 =
                       let uu____4445 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4446 = close_lopt lopt  in
                       (uu____4445, body, uu____4446)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4428  in
                   FStar_Syntax_Syntax.mk uu____4427  in
                 uu____4420 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos)
  
let arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____4488 ->
          let uu____4495 =
            let uu____4502 =
              let uu____4503 =
                let uu____4516 = FStar_Syntax_Subst.close_binders bs  in
                let uu____4517 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____4516, uu____4517)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4503  in
            FStar_Syntax_Syntax.mk uu____4502  in
          uu____4495 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____4552 =
        let uu____4553 = FStar_Syntax_Subst.compress t  in
        uu____4553.FStar_Syntax_Syntax.n  in
      match uu____4552 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____4579) ->
               let uu____4588 =
                 let uu____4589 = FStar_Syntax_Subst.compress tres  in
                 uu____4589.FStar_Syntax_Syntax.n  in
               (match uu____4588 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____4624 -> t)
           | uu____4625 -> t)
      | uu____4626 -> t
  
let refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____4639 =
        let uu____4640 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____4640 t.FStar_Syntax_Syntax.pos  in
      let uu____4641 =
        let uu____4648 =
          let uu____4649 =
            let uu____4656 =
              let uu____4657 =
                let uu____4658 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____4658]  in
              FStar_Syntax_Subst.close uu____4657 t  in
            (b, uu____4656)  in
          FStar_Syntax_Syntax.Tm_refine uu____4649  in
        FStar_Syntax_Syntax.mk uu____4648  in
      uu____4641 FStar_Pervasives_Native.None uu____4639
  
let branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____4711 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____4711 with
         | (bs1,c1) ->
             let uu____4728 = is_total_comp c1  in
             if uu____4728
             then
               let uu____4739 = arrow_formals_comp (comp_result c1)  in
               (match uu____4739 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____4785;
           FStar_Syntax_Syntax.index = uu____4786;
           FStar_Syntax_Syntax.sort = k2;_},uu____4788)
        -> arrow_formals_comp k2
    | uu____4795 ->
        let uu____4796 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4796)
  
let rec arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let uu____4824 = arrow_formals_comp k  in
    match uu____4824 with | (bs,c) -> (bs, (comp_result c))
  
let abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.residual_comp
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____4906 =
            let uu___59_4907 = rc  in
            let uu____4908 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___59_4907.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____4908;
              FStar_Syntax_Syntax.residual_flags =
                (uu___59_4907.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____4906
      | uu____4915 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____4947 =
        let uu____4948 =
          let uu____4951 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____4951  in
        uu____4948.FStar_Syntax_Syntax.n  in
      match uu____4947 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____4989 = aux t2 what  in
          (match uu____4989 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____5049 -> ([], t1, abs_body_lcomp)  in
    let uu____5062 = aux t FStar_Pervasives_Native.None  in
    match uu____5062 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____5104 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____5104 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let mk_letbinding :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
              -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding
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
  
let close_univs_and_mk_letbinding :
  FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Ident.ident Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
                -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding
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
                    | (FStar_Pervasives_Native.None ,uu____5265) -> def
                    | (uu____5276,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____5288) ->
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
  
let open_univ_vars_binders_and_comp :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                          FStar_Pervasives_Native.tuple2
                                          Prims.list,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple3
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____5394 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____5394 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5423 ->
            let t' = arrow binders c  in
            let uu____5433 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5433 with
             | (uvs1,t'1) ->
                 let uu____5452 =
                   let uu____5453 = FStar_Syntax_Subst.compress t'1  in
                   uu____5453.FStar_Syntax_Syntax.n  in
                 (match uu____5452 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____5494 -> failwith "Impossible"))
  
let is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____5513 -> false
  
let is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____5520 -> false
  
let is_lid_equality : FStar_Ident.lident -> Prims.bool =
  fun x  -> FStar_Ident.lid_equals x FStar_Parser_Const.eq2_lid 
let is_forall : FStar_Ident.lident -> Prims.bool =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.forall_lid 
let is_exists : FStar_Ident.lident -> Prims.bool =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.exists_lid 
let is_qlid : FStar_Ident.lident -> Prims.bool =
  fun lid  -> (is_forall lid) || (is_exists lid) 
let is_equality :
  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.bool =
  fun x  -> is_lid_equality x.FStar_Syntax_Syntax.v 
let lid_is_connective : FStar_Ident.lident -> Prims.bool =
  let lst =
    [FStar_Parser_Const.and_lid;
    FStar_Parser_Const.or_lid;
    FStar_Parser_Const.not_lid;
    FStar_Parser_Const.iff_lid;
    FStar_Parser_Const.imp_lid]  in
  fun lid  -> FStar_Util.for_some (FStar_Ident.lid_equals lid) lst 
let is_constructor :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____5568 =
        let uu____5569 = pre_typ t  in uu____5569.FStar_Syntax_Syntax.n  in
      match uu____5568 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____5573 -> false
  
let rec is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____5584 =
        let uu____5585 = pre_typ t  in uu____5585.FStar_Syntax_Syntax.n  in
      match uu____5584 with
      | FStar_Syntax_Syntax.Tm_fvar uu____5588 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____5590) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5612) ->
          is_constructed_typ t1 lid
      | uu____5617 -> false
  
let rec get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____5628 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____5629 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____5630 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5632) -> get_tycon t2
    | uu____5653 -> FStar_Pervasives_Native.None
  
let is_interpreted : FStar_Ident.lident -> Prims.bool =
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
  
let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____5667 =
      let uu____5668 = un_uinst t  in uu____5668.FStar_Syntax_Syntax.n  in
    match uu____5667 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____5672 -> false
  
let is_builtin_tactic : FStar_Ident.lident -> Prims.bool =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.lift_native_int (2))
    then
      let uu____5679 =
        let uu____5682 = FStar_List.splitAt (Prims.lift_native_int (2)) path
           in
        FStar_Pervasives_Native.fst uu____5682  in
      match uu____5679 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____5695 -> false
    else false
  
let ktype : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let ktype0 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let type_u :
  unit ->
    (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____5711  ->
    let u =
      let uu____5717 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_5  -> FStar_Syntax_Syntax.U_unif _0_5)
        uu____5717
       in
    let uu____5734 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____5734, u)
  
let attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun a  ->
    fun a'  ->
      let uu____5749 = eq_tm a a'  in
      match uu____5749 with | Equal  -> true | uu____5750 -> false
  
let attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  let uu____5753 =
    let uu____5760 =
      let uu____5761 =
        let uu____5762 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____5762
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____5761  in
    FStar_Syntax_Syntax.mk uu____5760  in
  uu____5753 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let exp_true_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let exp_false_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let exp_unit : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let exp_int : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_int (s, FStar_Pervasives_Native.None)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let exp_char : FStar_BaseTypes.char -> FStar_Syntax_Syntax.term =
  fun c  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let exp_string : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (s, FStar_Range.dummyRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let fvar_const : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
      FStar_Pervasives_Native.None
  
let tand : FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.and_lid 
let tor : FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.or_lid 
let timp : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.lift_native_int (1)))
    FStar_Pervasives_Native.None
  
let tiff : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.lift_native_int (2)))
    FStar_Pervasives_Native.None
  
let t_bool : FStar_Syntax_Syntax.term =
  fvar_const FStar_Parser_Const.bool_lid 
let b2t_v : FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.b2t_lid 
let t_not : FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.not_lid 
let t_false : FStar_Syntax_Syntax.term =
  fvar_const FStar_Parser_Const.false_lid 
let t_true : FStar_Syntax_Syntax.term =
  fvar_const FStar_Parser_Const.true_lid 
let tac_opaque_attr : FStar_Syntax_Syntax.term = exp_string "tac_opaque" 
let dm4f_bind_range_attr : FStar_Syntax_Syntax.term =
  fvar_const FStar_Parser_Const.dm4f_bind_range_attr 
let fail_attr : FStar_Syntax_Syntax.term =
  fvar_const FStar_Parser_Const.fail_attr 
let mk_conj_opt :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu____5821 =
            let uu____5824 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____5825 =
              let uu____5832 =
                let uu____5833 =
                  let uu____5848 =
                    let uu____5851 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____5852 =
                      let uu____5855 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____5855]  in
                    uu____5851 :: uu____5852  in
                  (tand, uu____5848)  in
                FStar_Syntax_Syntax.Tm_app uu____5833  in
              FStar_Syntax_Syntax.mk uu____5832  in
            uu____5825 FStar_Pervasives_Native.None uu____5824  in
          FStar_Pervasives_Native.Some uu____5821
  
let mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____5884 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____5885 =
          let uu____5892 =
            let uu____5893 =
              let uu____5908 =
                let uu____5911 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____5912 =
                  let uu____5915 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____5915]  in
                uu____5911 :: uu____5912  in
              (op_t, uu____5908)  in
            FStar_Syntax_Syntax.Tm_app uu____5893  in
          FStar_Syntax_Syntax.mk uu____5892  in
        uu____5885 FStar_Pervasives_Native.None uu____5884
  
let mk_neg :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun phi  ->
    let uu____5930 =
      let uu____5937 =
        let uu____5938 =
          let uu____5953 =
            let uu____5956 = FStar_Syntax_Syntax.as_arg phi  in [uu____5956]
             in
          (t_not, uu____5953)  in
        FStar_Syntax_Syntax.Tm_app uu____5938  in
      FStar_Syntax_Syntax.mk uu____5937  in
    uu____5930 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
let mk_conj :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun phi1  -> fun phi2  -> mk_binop tand phi1 phi2 
let mk_conj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
  
let mk_disj :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun phi1  -> fun phi2  -> mk_binop tor phi1 phi2 
let mk_disj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
  
let mk_imp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun phi1  -> fun phi2  -> mk_binop timp phi1 phi2 
let mk_iff :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun phi1  -> fun phi2  -> mk_binop tiff phi1 phi2 
let b2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun e  ->
    let uu____6039 =
      let uu____6046 =
        let uu____6047 =
          let uu____6062 =
            let uu____6065 = FStar_Syntax_Syntax.as_arg e  in [uu____6065]
             in
          (b2t_v, uu____6062)  in
        FStar_Syntax_Syntax.Tm_app uu____6047  in
      FStar_Syntax_Syntax.mk uu____6046  in
    uu____6039 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let teq : FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.eq2_lid 
let mk_untyped_eq2 :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun e1  ->
    fun e2  ->
      let uu____6083 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____6084 =
        let uu____6091 =
          let uu____6092 =
            let uu____6107 =
              let uu____6110 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____6111 =
                let uu____6114 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____6114]  in
              uu____6110 :: uu____6111  in
            (teq, uu____6107)  in
          FStar_Syntax_Syntax.Tm_app uu____6092  in
        FStar_Syntax_Syntax.mk uu____6091  in
      uu____6084 FStar_Pervasives_Native.None uu____6083
  
let mk_eq2 :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun u  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          let eq_inst = FStar_Syntax_Syntax.mk_Tm_uinst teq [u]  in
          let uu____6141 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____6142 =
            let uu____6149 =
              let uu____6150 =
                let uu____6165 =
                  let uu____6168 = FStar_Syntax_Syntax.iarg t  in
                  let uu____6169 =
                    let uu____6172 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____6173 =
                      let uu____6176 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____6176]  in
                    uu____6172 :: uu____6173  in
                  uu____6168 :: uu____6169  in
                (eq_inst, uu____6165)  in
              FStar_Syntax_Syntax.Tm_app uu____6150  in
            FStar_Syntax_Syntax.mk uu____6149  in
          uu____6142 FStar_Pervasives_Native.None uu____6141
  
let mk_has_type :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
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
        let uu____6205 =
          let uu____6212 =
            let uu____6213 =
              let uu____6228 =
                let uu____6231 = FStar_Syntax_Syntax.iarg t  in
                let uu____6232 =
                  let uu____6235 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____6236 =
                    let uu____6239 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____6239]  in
                  uu____6235 :: uu____6236  in
                uu____6231 :: uu____6232  in
              (t_has_type1, uu____6228)  in
            FStar_Syntax_Syntax.Tm_app uu____6213  in
          FStar_Syntax_Syntax.mk uu____6212  in
        uu____6205 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let mk_with_type :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
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
        let uu____6270 =
          let uu____6277 =
            let uu____6278 =
              let uu____6293 =
                let uu____6296 = FStar_Syntax_Syntax.iarg t  in
                let uu____6297 =
                  let uu____6300 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____6300]  in
                uu____6296 :: uu____6297  in
              (t_with_type1, uu____6293)  in
            FStar_Syntax_Syntax.Tm_app uu____6278  in
          FStar_Syntax_Syntax.mk uu____6277  in
        uu____6270 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let lex_t : FStar_Syntax_Syntax.term =
  fvar_const FStar_Parser_Const.lex_t_lid 
let lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  let uu____6310 =
    let uu____6317 =
      let uu____6318 =
        let uu____6325 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____6325, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____6318  in
    FStar_Syntax_Syntax.mk uu____6317  in
  uu____6310 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let lex_pair : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let tforall : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.lift_native_int (1)))
    FStar_Pervasives_Native.None
  
let t_haseq : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
  
let lcomp_of_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.lcomp
  =
  fun c0  ->
    let uu____6340 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____6353 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____6364 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____6340 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____6385  -> c0)
  
let mk_residual_comp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.cflags Prims.list ->
        FStar_Syntax_Syntax.residual_comp
  =
  fun l  ->
    fun t  ->
      fun f  ->
        {
          FStar_Syntax_Syntax.residual_effect = l;
          FStar_Syntax_Syntax.residual_typ = t;
          FStar_Syntax_Syntax.residual_flags = f
        }
  
let residual_tot :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.residual_comp
  =
  fun t  ->
    {
      FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid;
      FStar_Syntax_Syntax.residual_typ = (FStar_Pervasives_Native.Some t);
      FStar_Syntax_Syntax.residual_flags = [FStar_Syntax_Syntax.TOTAL]
    }
  
let residual_comp_of_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.residual_comp =
  fun c  ->
    {
      FStar_Syntax_Syntax.residual_effect = (comp_effect_name c);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (comp_result c));
      FStar_Syntax_Syntax.residual_flags = (comp_flags c)
    }
  
let residual_comp_of_lcomp :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.residual_comp =
  fun lc  ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.FStar_Syntax_Syntax.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.FStar_Syntax_Syntax.cflags)
    }
  
let mk_forall_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun fa  ->
    fun x  ->
      fun body  ->
        let uu____6459 =
          let uu____6466 =
            let uu____6467 =
              let uu____6482 =
                let uu____6485 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____6486 =
                  let uu____6489 =
                    let uu____6490 =
                      let uu____6491 =
                        let uu____6492 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____6492]  in
                      abs uu____6491 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____6490  in
                  [uu____6489]  in
                uu____6485 :: uu____6486  in
              (fa, uu____6482)  in
            FStar_Syntax_Syntax.Tm_app uu____6467  in
          FStar_Syntax_Syntax.mk uu____6466  in
        uu____6459 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let mk_forall_no_univ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  = fun x  -> fun body  -> mk_forall_aux tforall x body 
let mk_forall :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun u  ->
    fun x  ->
      fun body  ->
        let tforall1 = FStar_Syntax_Syntax.mk_Tm_uinst tforall [u]  in
        mk_forall_aux tforall1 x body
  
let close_forall_no_univs :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____6545 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____6545
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____6556 -> true
    | uu____6557 -> false
  
let if_then_else :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t1  ->
      fun t2  ->
        let then_branch =
          let uu____6602 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____6602, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____6630 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____6630, FStar_Pervasives_Native.None, t2)  in
        let uu____6643 =
          let uu____6644 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____6644  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____6643
  
let mk_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level
             (Prims.lift_native_int (1))) FStar_Pervasives_Native.None
         in
      let uu____6718 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6721 =
        let uu____6730 = FStar_Syntax_Syntax.as_arg p  in [uu____6730]  in
      mk_app uu____6718 uu____6721
  
let mk_auto_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level
             (Prims.lift_native_int (2))) FStar_Pervasives_Native.None
         in
      let uu____6744 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6747 =
        let uu____6756 = FStar_Syntax_Syntax.as_arg p  in [uu____6756]  in
      mk_app uu____6744 uu____6747
  
let un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____6766 = head_and_args t  in
    match uu____6766 with
    | (head1,args) ->
        let uu____6807 =
          let uu____6820 =
            let uu____6821 = un_uinst head1  in
            uu____6821.FStar_Syntax_Syntax.n  in
          (uu____6820, args)  in
        (match uu____6807 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____6838)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____6890 =
                    let uu____6895 =
                      let uu____6896 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____6896]  in
                    FStar_Syntax_Subst.open_term uu____6895 p  in
                  (match uu____6890 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____6925 -> failwith "impossible"  in
                       let uu____6930 =
                         let uu____6931 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____6931
                          in
                       if uu____6930
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____6941 -> FStar_Pervasives_Native.None)
         | uu____6944 -> FStar_Pervasives_Native.None)
  
let is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____6972 = head_and_args t  in
    match uu____6972 with
    | (head1,args) ->
        let uu____7017 =
          let uu____7030 =
            let uu____7031 = FStar_Syntax_Subst.compress head1  in
            uu____7031.FStar_Syntax_Syntax.n  in
          (uu____7030, args)  in
        (match uu____7017 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____7051;
               FStar_Syntax_Syntax.vars = uu____7052;_},u::[]),(t1,uu____7055)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____7094 -> FStar_Pervasives_Native.None)
  
let is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____7126 = head_and_args t  in
    match uu____7126 with
    | (head1,args) ->
        let uu____7171 =
          let uu____7184 =
            let uu____7185 = FStar_Syntax_Subst.compress head1  in
            uu____7185.FStar_Syntax_Syntax.n  in
          (uu____7184, args)  in
        (match uu____7171 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____7205;
               FStar_Syntax_Syntax.vars = uu____7206;_},u::[]),(t1,uu____7209)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____7248 -> FStar_Pervasives_Native.None)
  
let is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____7272 = let uu____7287 = unmeta t  in head_and_args uu____7287
       in
    match uu____7272 with
    | (head1,uu____7289) ->
        let uu____7310 =
          let uu____7311 = un_uinst head1  in
          uu____7311.FStar_Syntax_Syntax.n  in
        (match uu____7310 with
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
         | uu____7315 -> false)
  
let arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____7333 =
      let uu____7346 =
        let uu____7347 = FStar_Syntax_Subst.compress t  in
        uu____7347.FStar_Syntax_Syntax.n  in
      match uu____7346 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____7456 =
            let uu____7465 =
              let uu____7466 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____7466  in
            (b, uu____7465)  in
          FStar_Pervasives_Native.Some uu____7456
      | uu____7479 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____7333
      (fun uu____7515  ->
         match uu____7515 with
         | (b,c) ->
             let uu____7550 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____7550 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____7597 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun bv  ->
    fun t  ->
      let uu____7624 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____7624
  
type qpats = FStar_Syntax_Syntax.args Prims.list[@@deriving show]
type connective =
  | QAll of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3 
  | QEx of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3 
  | BaseConn of (FStar_Ident.lident,FStar_Syntax_Syntax.args)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let uu___is_QAll : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____7672 -> false
  
let __proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let uu___is_QEx : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____7710 -> false
  
let __proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let uu___is_BaseConn : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____7746 -> false
  
let __proj__BaseConn__item___0 :
  connective ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | BaseConn _0 -> _0 
let destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1  in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____7783) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____7795) ->
          unmeta_monadic t
      | uu____7808 -> f2  in
    let destruct_base_conn f1 =
      let connectives =
        [(FStar_Parser_Const.true_lid, (Prims.lift_native_int (0)));
        (FStar_Parser_Const.false_lid, (Prims.lift_native_int (0)));
        (FStar_Parser_Const.and_lid, (Prims.lift_native_int (2)));
        (FStar_Parser_Const.or_lid, (Prims.lift_native_int (2)));
        (FStar_Parser_Const.imp_lid, (Prims.lift_native_int (2)));
        (FStar_Parser_Const.iff_lid, (Prims.lift_native_int (2)));
        (FStar_Parser_Const.ite_lid, (Prims.lift_native_int (3)));
        (FStar_Parser_Const.not_lid, (Prims.lift_native_int (1)));
        (FStar_Parser_Const.eq2_lid, (Prims.lift_native_int (3)));
        (FStar_Parser_Const.eq2_lid, (Prims.lift_native_int (2)));
        (FStar_Parser_Const.eq3_lid, (Prims.lift_native_int (4)));
        (FStar_Parser_Const.eq3_lid, (Prims.lift_native_int (2)))]  in
      let aux f2 uu____7892 =
        match uu____7892 with
        | (lid,arity) ->
            let uu____7901 =
              let uu____7916 = unmeta_monadic f2  in head_and_args uu____7916
               in
            (match uu____7901 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____7942 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____7942
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____8019 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____8019)
      | uu____8030 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____8085 = head_and_args t1  in
        match uu____8085 with
        | (t2,args) ->
            let uu____8132 = un_uinst t2  in
            let uu____8133 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____8166  ->
                      match uu____8166 with
                      | (t3,imp) ->
                          let uu____8177 = unascribe t3  in (uu____8177, imp)))
               in
            (uu____8132, uu____8133)
         in
      let rec aux qopt out t1 =
        let uu____8218 = let uu____8235 = flat t1  in (qopt, uu____8235)  in
        match uu____8218 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____8262;
                 FStar_Syntax_Syntax.vars = uu____8263;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____8266);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____8267;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____8268;_},uu____8269)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____8346;
                 FStar_Syntax_Syntax.vars = uu____8347;_},uu____8348::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____8351);
                  FStar_Syntax_Syntax.pos = uu____8352;
                  FStar_Syntax_Syntax.vars = uu____8353;_},uu____8354)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____8442;
               FStar_Syntax_Syntax.vars = uu____8443;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____8446);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8447;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8448;_},uu____8449)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____8520 =
              let uu____8523 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____8523  in
            aux uu____8520 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____8529;
               FStar_Syntax_Syntax.vars = uu____8530;_},uu____8531::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____8534);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____8535;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____8536;_},uu____8537)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____8620 =
              let uu____8623 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____8623  in
            aux uu____8620 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____8629) ->
            let bs = FStar_List.rev out  in
            let uu____8663 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____8663 with
             | (bs1,t2) ->
                 let uu____8672 = patterns t2  in
                 (match uu____8672 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____8734 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let u_connectives =
      [(FStar_Parser_Const.true_lid, FStar_Parser_Const.c_true_lid,
         (Prims.lift_native_int (0)));
      (FStar_Parser_Const.false_lid, FStar_Parser_Const.c_false_lid,
        (Prims.lift_native_int (0)));
      (FStar_Parser_Const.and_lid, FStar_Parser_Const.c_and_lid,
        (Prims.lift_native_int (2)));
      (FStar_Parser_Const.or_lid, FStar_Parser_Const.c_or_lid,
        (Prims.lift_native_int (2)))]
       in
    let destruct_sq_base_conn t =
      let uu____8802 = un_squash t  in
      FStar_Util.bind_opt uu____8802
        (fun t1  ->
           let uu____8818 = head_and_args' t1  in
           match uu____8818 with
           | (hd1,args) ->
               let uu____8851 =
                 let uu____8856 =
                   let uu____8857 = un_uinst hd1  in
                   uu____8857.FStar_Syntax_Syntax.n  in
                 (uu____8856, (FStar_List.length args))  in
               (match uu____8851 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_6) when
                    (_0_6 = (Prims.lift_native_int (2))) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_7) when
                    (_0_7 = (Prims.lift_native_int (2))) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_8) when
                    (_0_8 = (Prims.lift_native_int (2))) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_9) when
                    (_0_9 = (Prims.lift_native_int (3))) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_10) when
                    (_0_10 = (Prims.lift_native_int (2))) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_11) when
                    (_0_11 = (Prims.lift_native_int (4))) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_12) when
                    (_0_12 = (Prims.lift_native_int (0))) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_13) when
                    (_0_13 = (Prims.lift_native_int (0))) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____8940 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____8969 = un_squash t  in
      FStar_Util.bind_opt uu____8969
        (fun t1  ->
           let uu____8984 = arrow_one t1  in
           match uu____8984 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____8999 =
                 let uu____9000 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____9000  in
               if uu____8999
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____9007 = comp_to_comp_typ_nouniv c  in
                    uu____9007.FStar_Syntax_Syntax.result_typ  in
                  let uu____9008 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____9008
                  then
                    let uu____9011 = patterns q  in
                    match uu____9011 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____9067 =
                       let uu____9068 =
                         let uu____9073 =
                           let uu____9076 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____9077 =
                             let uu____9080 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____9080]  in
                           uu____9076 :: uu____9077  in
                         (FStar_Parser_Const.imp_lid, uu____9073)  in
                       BaseConn uu____9068  in
                     FStar_Pervasives_Native.Some uu____9067))
           | uu____9083 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____9091 = un_squash t  in
      FStar_Util.bind_opt uu____9091
        (fun t1  ->
           let uu____9122 = head_and_args' t1  in
           match uu____9122 with
           | (hd1,args) ->
               let uu____9155 =
                 let uu____9168 =
                   let uu____9169 = un_uinst hd1  in
                   uu____9169.FStar_Syntax_Syntax.n  in
                 (uu____9168, args)  in
               (match uu____9155 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____9184)::(a2,uu____9186)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____9221 =
                      let uu____9222 = FStar_Syntax_Subst.compress a2  in
                      uu____9222.FStar_Syntax_Syntax.n  in
                    (match uu____9221 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____9229) ->
                         let uu____9256 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____9256 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____9295 -> failwith "impossible"  in
                              let uu____9300 = patterns q1  in
                              (match uu____9300 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____9367 -> FStar_Pervasives_Native.None)
                | uu____9368 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____9389 = destruct_sq_forall phi  in
          (match uu____9389 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____9411 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____9417 = destruct_sq_exists phi  in
          (match uu____9417 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____9439 -> f1)
      | uu____9442 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____9446 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____9446
      (fun uu____9451  ->
         let uu____9452 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____9452
           (fun uu____9457  ->
              let uu____9458 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____9458
                (fun uu____9463  ->
                   let uu____9464 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____9464
                     (fun uu____9469  ->
                        let uu____9470 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____9470
                          (fun uu____9474  -> FStar_Pervasives_Native.None)))))
  
let unthunk_lemma_post :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let uu____9482 =
      let uu____9483 = FStar_Syntax_Subst.compress t  in
      uu____9483.FStar_Syntax_Syntax.n  in
    match uu____9482 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____9490) ->
        let uu____9517 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____9517 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____9543 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____9543
             then
               let uu____9546 =
                 let uu____9555 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____9555]  in
               mk_app t uu____9546
             else e1)
    | uu____9557 ->
        let uu____9558 =
          let uu____9567 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____9567]  in
        mk_app t uu____9558
  
let action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____9584 =
            let uu____9589 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.Delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____9589  in
          let uu____9590 =
            let uu____9591 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____9591  in
          let uu____9594 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____9584 a.FStar_Syntax_Syntax.action_univs uu____9590
            FStar_Parser_Const.effect_Tot_lid uu____9594 [] pos
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
  
let mk_reify :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let reify_ =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
       in
    let uu____9623 =
      let uu____9630 =
        let uu____9631 =
          let uu____9646 =
            let uu____9649 = FStar_Syntax_Syntax.as_arg t  in [uu____9649]
             in
          (reify_, uu____9646)  in
        FStar_Syntax_Syntax.Tm_app uu____9631  in
      FStar_Syntax_Syntax.mk uu____9630  in
    uu____9623 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____9663 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____9689 = unfold_lazy i  in delta_qualifier uu____9689
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____9691 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____9692 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____9693 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____9716 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____9733 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____9734 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____9741 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____9742 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____9756) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____9761;
           FStar_Syntax_Syntax.index = uu____9762;
           FStar_Syntax_Syntax.sort = t2;_},uu____9764)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____9772) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____9778,uu____9779) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____9821) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____9842,t2,uu____9844) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____9865,t2) -> delta_qualifier t2
  
let rec incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth =
  fun d  ->
    match d with
    | FStar_Syntax_Syntax.Delta_equational  -> d
    | FStar_Syntax_Syntax.Delta_constant  ->
        FStar_Syntax_Syntax.Delta_defined_at_level
          (Prims.lift_native_int (1))
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        FStar_Syntax_Syntax.Delta_defined_at_level
          (i + (Prims.lift_native_int (1)))
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
  
let incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let uu____9895 = delta_qualifier t  in incr_delta_depth uu____9895
  
let is_unknown : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____9901 =
      let uu____9902 = FStar_Syntax_Subst.compress t  in
      uu____9902.FStar_Syntax_Syntax.n  in
    match uu____9901 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____9905 -> false
  
let rec list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____9919 = let uu____9934 = unmeta e  in head_and_args uu____9934
       in
    match uu____9919 with
    | (head1,args) ->
        let uu____9961 =
          let uu____9974 =
            let uu____9975 = un_uinst head1  in
            uu____9975.FStar_Syntax_Syntax.n  in
          (uu____9974, args)  in
        (match uu____9961 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9991) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____10011::(hd1,uu____10013)::(tl1,uu____10015)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____10062 =
               let uu____10067 =
                 let uu____10072 = list_elements tl1  in
                 FStar_Util.must uu____10072  in
               hd1 :: uu____10067  in
             FStar_Pervasives_Native.Some uu____10062
         | uu____10085 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____10106 .
    ('Auu____10106 -> 'Auu____10106) ->
      'Auu____10106 Prims.list -> 'Auu____10106 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____10131 = f a  in [uu____10131]
      | x::xs -> let uu____10136 = apply_last f xs  in x :: uu____10136
  
let dm4f_lid :
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident =
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
  
let rec mk_list :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____10182 =
            let uu____10189 =
              let uu____10190 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____10190  in
            FStar_Syntax_Syntax.mk uu____10189  in
          uu____10182 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____10207 =
            let uu____10212 =
              let uu____10213 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____10213
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____10212 args  in
          uu____10207 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____10229 =
            let uu____10234 =
              let uu____10235 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____10235
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____10234 args  in
          uu____10229 FStar_Pervasives_Native.None pos  in
        let uu____10238 =
          let uu____10239 =
            let uu____10240 = FStar_Syntax_Syntax.iarg typ  in [uu____10240]
             in
          nil uu____10239 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____10246 =
                 let uu____10247 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____10248 =
                   let uu____10251 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____10252 =
                     let uu____10255 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____10255]  in
                   uu____10251 :: uu____10252  in
                 uu____10247 :: uu____10248  in
               cons1 uu____10246 t.FStar_Syntax_Syntax.pos) l uu____10238
  
let uvar_from_id :
  Prims.int ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun id1  ->
    fun t  ->
      let uu____10268 =
        let uu____10275 =
          let uu____10276 =
            let uu____10293 = FStar_Syntax_Unionfind.from_id id1  in
            (uu____10293, t)  in
          FStar_Syntax_Syntax.Tm_uvar uu____10276  in
        FStar_Syntax_Syntax.mk uu____10275  in
      uu____10268 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        | uu____10360 -> false
  
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
          | uu____10467 -> false
  
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
        | uu____10622 -> false
  
let debug_term_eq : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let check : Prims.string -> Prims.bool -> Prims.bool =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____10656 = FStar_ST.op_Bang debug_term_eq  in
          if uu____10656
          then FStar_Util.print1 ">>> term_eq failing: %s\n" msg
          else ());
         false)
  
let fail : Prims.string -> Prims.bool = fun msg  -> check msg false 
let rec term_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool
  =
  fun dbg  ->
    fun t1  ->
      fun t2  ->
        let t11 = let uu____10844 = unmeta_safe t1  in canon_app uu____10844
           in
        let t21 = let uu____10848 = unmeta_safe t2  in canon_app uu____10848
           in
        let uu____10849 =
          let uu____10854 =
            let uu____10855 =
              let uu____10858 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____10858  in
            uu____10855.FStar_Syntax_Syntax.n  in
          let uu____10859 =
            let uu____10860 =
              let uu____10863 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____10863  in
            uu____10860.FStar_Syntax_Syntax.n  in
          (uu____10854, uu____10859)  in
        match uu____10849 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____10864,uu____10865) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10872,FStar_Syntax_Syntax.Tm_uinst uu____10873) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____10880,uu____10881) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10906,FStar_Syntax_Syntax.Tm_delayed uu____10907) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____10932,uu____10933) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10960,FStar_Syntax_Syntax.Tm_ascribed uu____10961) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____10994 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____10994
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____10997 = FStar_Const.eq_const c1 c2  in
            check "const" uu____10997
        | (FStar_Syntax_Syntax.Tm_type
           uu____10998,FStar_Syntax_Syntax.Tm_type uu____10999) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____11048 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____11048) &&
              (let uu____11054 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____11054)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____11093 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____11093) &&
              (let uu____11099 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____11099)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____11113 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____11113)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____11160 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____11160) &&
              (let uu____11162 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____11162)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____11247 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____11247) &&
              (let uu____11249 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____11249)
        | (FStar_Syntax_Syntax.Tm_lazy uu____11264,uu____11265) ->
            let uu____11266 =
              let uu____11267 = unlazy t11  in
              term_eq_dbg dbg uu____11267 t21  in
            check "lazy_l" uu____11266
        | (uu____11268,FStar_Syntax_Syntax.Tm_lazy uu____11269) ->
            let uu____11270 =
              let uu____11271 = unlazy t21  in
              term_eq_dbg dbg t11 uu____11271  in
            check "lazy_r" uu____11270
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____11307 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____11307))
              &&
              (let uu____11309 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____11309)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____11311),FStar_Syntax_Syntax.Tm_uvar (u2,uu____11313)) ->
            check "uvar" (u1 = u2)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (check "tm_quoted qi" (qi1 = qi2)) &&
              (let uu____11385 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____11385)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____11412 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____11412) &&
                   (let uu____11414 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____11414)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____11431 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____11431) &&
                    (let uu____11433 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____11433))
                   &&
                   (let uu____11435 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____11435)
             | uu____11436 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____11441) -> fail "unk"
        | (uu____11442,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____11443,uu____11444) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____11445,uu____11446) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____11447,uu____11448) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____11449,uu____11450) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____11451,uu____11452) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____11453,uu____11454) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____11471,uu____11472) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____11485,uu____11486) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____11493,uu____11494) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____11509,uu____11510) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____11533,uu____11534) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____11547,uu____11548) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____11565,uu____11566) ->
            fail "bottom"
        | (uu____11573,FStar_Syntax_Syntax.Tm_bvar uu____11574) ->
            fail "bottom"
        | (uu____11575,FStar_Syntax_Syntax.Tm_name uu____11576) ->
            fail "bottom"
        | (uu____11577,FStar_Syntax_Syntax.Tm_fvar uu____11578) ->
            fail "bottom"
        | (uu____11579,FStar_Syntax_Syntax.Tm_constant uu____11580) ->
            fail "bottom"
        | (uu____11581,FStar_Syntax_Syntax.Tm_type uu____11582) ->
            fail "bottom"
        | (uu____11583,FStar_Syntax_Syntax.Tm_abs uu____11584) ->
            fail "bottom"
        | (uu____11601,FStar_Syntax_Syntax.Tm_arrow uu____11602) ->
            fail "bottom"
        | (uu____11615,FStar_Syntax_Syntax.Tm_refine uu____11616) ->
            fail "bottom"
        | (uu____11623,FStar_Syntax_Syntax.Tm_app uu____11624) ->
            fail "bottom"
        | (uu____11639,FStar_Syntax_Syntax.Tm_match uu____11640) ->
            fail "bottom"
        | (uu____11663,FStar_Syntax_Syntax.Tm_let uu____11664) ->
            fail "bottom"
        | (uu____11677,FStar_Syntax_Syntax.Tm_uvar uu____11678) ->
            fail "bottom"
        | (uu____11695,FStar_Syntax_Syntax.Tm_meta uu____11696) ->
            fail "bottom"

and arg_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun dbg  ->
    fun a1  ->
      fun a2  ->
        eqprod
          (fun t1  ->
             fun t2  ->
               let uu____11723 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____11723)
          (fun q1  -> fun q2  -> check "arg qual" (q1 = q2)) a1 a2

and binder_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun dbg  ->
    fun b1  ->
      fun b2  ->
        eqprod
          (fun b11  ->
             fun b21  ->
               let uu____11744 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____11744)
          (fun q1  -> fun q2  -> check "binder qual" (q1 = q2)) b1 b2

and lcomp_eq_dbg :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c1  -> fun c2  -> fail "lcomp"

and residual_eq_dbg :
  FStar_Syntax_Syntax.residual_comp ->
    FStar_Syntax_Syntax.residual_comp -> Prims.bool
  = fun r1  -> fun r2  -> fail "residual"

and comp_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool
  =
  fun dbg  ->
    fun c1  ->
      fun c2  ->
        let c11 = comp_to_comp_typ_nouniv c1  in
        let c21 = comp_to_comp_typ_nouniv c2  in
        ((let uu____11764 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____11764) &&
           (let uu____11766 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____11766))
          && true

and eq_flags_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.cflags -> FStar_Syntax_Syntax.cflags -> Prims.bool
  = fun dbg  -> fun f1  -> fun f2  -> true

and branch_eq_dbg :
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
        FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun dbg  ->
    fun uu____11771  ->
      fun uu____11772  ->
        match (uu____11771, uu____11772) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____11897 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____11897) &&
               (let uu____11899 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____11899))
              &&
              (let uu____11901 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____11940 -> false  in
               check "branch when" uu____11901)

and letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____11958 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____11958) &&
           (let uu____11964 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____11964))
          &&
          (let uu____11966 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____11966)

let term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____11978 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____11978 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec sizeof : FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____12031 ->
        let uu____12056 =
          let uu____12057 = FStar_Syntax_Subst.compress t  in
          sizeof uu____12057  in
        (Prims.lift_native_int (1)) + uu____12056
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____12059 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.lift_native_int (1)) + uu____12059
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____12061 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.lift_native_int (1)) + uu____12061
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____12068 = sizeof t1  in (FStar_List.length us) + uu____12068
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____12071) ->
        let uu____12092 = sizeof t1  in
        let uu____12093 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____12104  ->
                 match uu____12104 with
                 | (bv,uu____12110) ->
                     let uu____12111 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____12111) (Prims.lift_native_int (0)) bs
           in
        uu____12092 + uu____12093
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____12134 = sizeof hd1  in
        let uu____12135 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____12146  ->
                 match uu____12146 with
                 | (arg,uu____12152) ->
                     let uu____12153 = sizeof arg  in acc + uu____12153)
            (Prims.lift_native_int (0)) args
           in
        uu____12134 + uu____12135
    | uu____12154 -> (Prims.lift_native_int (1))
  
let is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun lid  ->
    fun t  ->
      let uu____12165 =
        let uu____12166 = un_uinst t  in uu____12166.FStar_Syntax_Syntax.n
         in
      match uu____12165 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____12170 -> false
  
let is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  -> is_fvar FStar_Parser_Const.synth_lid t 
let has_attribute :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Ident.lident -> Prims.bool
  = fun attrs  -> fun attr  -> FStar_Util.for_some (is_fvar attr) attrs 
let process_pragma : FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit
  =
  fun p  ->
    fun r  ->
      let set_options1 t s =
        let uu____12211 = FStar_Options.set_options t s  in
        match uu____12211 with
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
          ((let uu____12219 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____12219 (fun a238  -> ()));
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
  
let rec unbound_variables :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv Prims.list =
  fun tm  ->
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____12239 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____12295 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____12296 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____12297 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____12306) ->
        let uu____12327 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____12327 with
         | (bs1,t2) ->
             let uu____12336 =
               FStar_List.collect
                 (fun uu____12346  ->
                    match uu____12346 with
                    | (b,uu____12354) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____12355 = unbound_variables t2  in
             FStar_List.append uu____12336 uu____12355)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____12376 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____12376 with
         | (bs1,c1) ->
             let uu____12385 =
               FStar_List.collect
                 (fun uu____12395  ->
                    match uu____12395 with
                    | (b,uu____12403) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____12404 = unbound_variables_comp c1  in
             FStar_List.append uu____12385 uu____12404)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____12413 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____12413 with
         | (bs,t2) ->
             let uu____12436 =
               FStar_List.collect
                 (fun uu____12446  ->
                    match uu____12446 with
                    | (b1,uu____12454) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____12455 = unbound_variables t2  in
             FStar_List.append uu____12436 uu____12455)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____12480 =
          FStar_List.collect
            (fun uu____12490  ->
               match uu____12490 with
               | (x,uu____12498) -> unbound_variables x) args
           in
        let uu____12499 = unbound_variables t1  in
        FStar_List.append uu____12480 uu____12499
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____12540 = unbound_variables t1  in
        let uu____12543 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____12572 = FStar_Syntax_Subst.open_branch br  in
                  match uu____12572 with
                  | (p,wopt,t2) ->
                      let uu____12594 = unbound_variables t2  in
                      let uu____12597 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____12594 uu____12597))
           in
        FStar_List.append uu____12540 uu____12543
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____12611) ->
        let uu____12652 = unbound_variables t1  in
        let uu____12655 =
          let uu____12658 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____12689 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____12658 uu____12689  in
        FStar_List.append uu____12652 uu____12655
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____12727 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____12730 =
          let uu____12733 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____12736 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____12741 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____12743 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____12743 with
                 | (uu____12764,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____12733 uu____12736  in
        FStar_List.append uu____12727 uu____12730
    | FStar_Syntax_Syntax.Tm_let ((uu____12766,lbs),t1) ->
        let uu____12783 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____12783 with
         | (lbs1,t2) ->
             let uu____12798 = unbound_variables t2  in
             let uu____12801 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____12808 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____12811 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____12808 uu____12811) lbs1
                in
             FStar_List.append uu____12798 uu____12801)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____12828 = unbound_variables t1  in
        let uu____12831 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____12860  ->
                      match uu____12860 with
                      | (a,uu____12868) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____12869,uu____12870,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____12876,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____12882 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____12889 -> []
          | FStar_Syntax_Syntax.Meta_named uu____12890 -> []  in
        FStar_List.append uu____12828 uu____12831

and unbound_variables_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.bv Prims.list =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____12895) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____12905) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____12915 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____12918 =
          FStar_List.collect
            (fun uu____12928  ->
               match uu____12928 with
               | (a,uu____12936) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____12915 uu____12918
