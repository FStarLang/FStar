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
            let uu____173 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____173
            then []
            else (let uu____185 = arg_of_non_null_binder b  in [uu____185])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  =
  fun binders  ->
    let uu____211 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____275 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____275
              then
                let b1 =
                  let uu____293 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____293, (FStar_Pervasives_Native.snd b))  in
                let uu____294 = arg_of_non_null_binder b1  in (b1, uu____294)
              else
                (let uu____308 = arg_of_non_null_binder b  in (b, uu____308))))
       in
    FStar_All.pipe_right uu____211 FStar_List.unzip
  
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
              let uu____408 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____408
              then
                let uu____413 = b  in
                match uu____413 with
                | (a,imp) ->
                    let b1 =
                      let uu____425 =
                        let uu____426 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____426  in
                      FStar_Ident.id_of_text uu____425  in
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
        let uu____460 =
          let uu____467 =
            let uu____468 =
              let uu____481 = name_binders binders  in (uu____481, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____468  in
          FStar_Syntax_Syntax.mk uu____467  in
        uu____460 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____499 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____535  ->
            match uu____535 with
            | (t,imp) ->
                let uu____546 =
                  let uu____547 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____547
                   in
                (uu____546, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____595  ->
            match uu____595 with
            | (t,imp) ->
                let uu____612 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____612, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____624 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____624
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____635 . 'Auu____635 -> 'Auu____635 Prims.list =
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
          (fun uu____731  ->
             fun uu____732  ->
               match (uu____731, uu____732) with
               | ((x,uu____750),(y,uu____752)) ->
                   let uu____761 =
                     let uu____768 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____768)  in
                   FStar_Syntax_Syntax.NT uu____761) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____781) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____787,uu____788) -> unmeta e2
    | uu____829 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____842 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____849 -> e1
         | uu____858 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____860,uu____861) ->
        unmeta_safe e2
    | uu____902 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____916 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____917 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____927 = univ_kernel u1  in
        (match uu____927 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____938 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____945 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____955 = univ_kernel u  in FStar_Pervasives_Native.snd uu____955
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____970,uu____971) ->
          failwith "Impossible: compare_univs"
      | (uu____972,FStar_Syntax_Syntax.U_bvar uu____973) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____974) ->
          ~- (Prims.parse_int "1")
      | (uu____975,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____976) -> ~- (Prims.parse_int "1")
      | (uu____977,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____980,FStar_Syntax_Syntax.U_unif
         uu____981) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____990,FStar_Syntax_Syntax.U_name
         uu____991) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____1018 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____1019 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____1018 - uu____1019
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____1050 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____1050
                 (fun uu____1065  ->
                    match uu____1065 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1079,uu____1080) ->
          ~- (Prims.parse_int "1")
      | (uu____1083,FStar_Syntax_Syntax.U_max uu____1084) ->
          (Prims.parse_int "1")
      | uu____1087 ->
          let uu____1092 = univ_kernel u1  in
          (match uu____1092 with
           | (k1,n1) ->
               let uu____1099 = univ_kernel u2  in
               (match uu____1099 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1118 = compare_univs u1 u2  in
      uu____1118 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1133 =
        let uu____1134 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1134;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1133
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1151 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1160 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1182 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1191 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1217 =
          let uu____1218 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1218  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1217;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1245 =
          let uu____1246 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1246  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1245;
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
      let uu___52_1279 = c  in
      let uu____1280 =
        let uu____1281 =
          let uu___53_1282 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___53_1282.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___53_1282.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___53_1282.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___53_1282.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1281  in
      {
        FStar_Syntax_Syntax.n = uu____1280;
        FStar_Syntax_Syntax.pos = (uu___52_1279.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___52_1279.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1307 -> c
        | FStar_Syntax_Syntax.GTotal uu____1316 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___54_1327 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___54_1327.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___54_1327.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___54_1327.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___54_1327.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___55_1328 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___55_1328.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___55_1328.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1331  ->
           let uu____1332 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1332)
  
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
    | uu____1367 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1378 -> true
    | FStar_Syntax_Syntax.GTotal uu____1387 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___40_1408  ->
               match uu___40_1408 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1409 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___41_1418  ->
               match uu___41_1418 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1419 -> false)))
  
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
            (fun uu___42_1428  ->
               match uu___42_1428 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1429 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___43_1442  ->
            match uu___43_1442 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1443 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___44_1452  ->
            match uu___44_1452 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1453 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1477 -> true
    | FStar_Syntax_Syntax.GTotal uu____1486 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___45_1499  ->
                   match uu___45_1499 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1500 -> false)))
  
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
            (fun uu___46_1528  ->
               match uu___46_1528 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1529 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1540 =
      let uu____1541 = FStar_Syntax_Subst.compress t  in
      uu____1541.FStar_Syntax_Syntax.n  in
    match uu____1540 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1544,c) -> is_pure_or_ghost_comp c
    | uu____1562 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1573 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1579 =
      let uu____1580 = FStar_Syntax_Subst.compress t  in
      uu____1580.FStar_Syntax_Syntax.n  in
    match uu____1579 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1583,c) -> is_lemma_comp c
    | uu____1601 -> false
  
let (head_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.term'
                                 FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____1664 -> (t1, [])
  
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
        let uu____1731 = head_and_args' head1  in
        (match uu____1731 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1788 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1810) ->
        FStar_Syntax_Subst.compress t2
    | uu____1815 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1821 =
      let uu____1822 = FStar_Syntax_Subst.compress t  in
      uu____1822.FStar_Syntax_Syntax.n  in
    match uu____1821 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1825,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1847)::uu____1848 ->
                  let pats' = unmeta pats  in
                  let uu____1892 = head_and_args pats'  in
                  (match uu____1892 with
                   | (head1,uu____1906) ->
                       let uu____1923 =
                         let uu____1924 = un_uinst head1  in
                         uu____1924.FStar_Syntax_Syntax.n  in
                       (match uu____1923 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1928 -> false))
              | uu____1929 -> false)
         | uu____1938 -> false)
    | uu____1939 -> false
  
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
                (fun uu___47_1953  ->
                   match uu___47_1953 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1954 -> false)))
    | uu____1955 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1970) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1980) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2008 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2017 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___56_2029 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___56_2029.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___56_2029.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___56_2029.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___56_2029.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___48_2042  ->
            match uu___48_2042 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2043 -> false))
  
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
    | uu____2063 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2071,uu____2072) ->
        unascribe e2
    | uu____2113 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2165,uu____2166) ->
          ascribe t' k
      | uu____2207 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2233 =
      let uu____2242 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2242  in
    uu____2233 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2301 =
      let uu____2302 = FStar_Syntax_Subst.compress t  in
      uu____2302.FStar_Syntax_Syntax.n  in
    match uu____2301 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2306 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2306
    | uu____2307 -> t
  
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
            let uu____2346 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2346;
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
    let uu____2358 =
      let uu____2371 = unascribe t  in head_and_args' uu____2371  in
    match uu____2358 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown [@@deriving show]
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2397 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2403 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2409 -> false
  
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
      let equal_if uu___49_2485 = if uu___49_2485 then Equal else Unknown  in
      let equal_iff uu___50_2492 = if uu___50_2492 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2510 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2522) -> NotEqual
        | (uu____2523,NotEqual ) -> NotEqual
        | (Unknown ,uu____2524) -> Unknown
        | (uu____2525,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____2571 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2571
        then
          let uu____2573 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2631  ->
                    match uu____2631 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2657 = eq_tm a1 a2  in
                        eq_inj acc uu____2657) Equal) uu____2573
        else NotEqual  in
      let uu____2659 =
        let uu____2664 =
          let uu____2665 = unmeta t11  in uu____2665.FStar_Syntax_Syntax.n
           in
        let uu____2668 =
          let uu____2669 = unmeta t21  in uu____2669.FStar_Syntax_Syntax.n
           in
        (uu____2664, uu____2668)  in
      match uu____2659 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2674,uu____2675) ->
          let uu____2676 = unlazy t11  in eq_tm uu____2676 t21
      | (uu____2677,FStar_Syntax_Syntax.Tm_lazy uu____2678) ->
          let uu____2679 = unlazy t21  in eq_tm t11 uu____2679
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
            (let uu____2697 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2697)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2710 = eq_tm f g  in
          eq_and uu____2710
            (fun uu____2713  ->
               let uu____2714 = eq_univs_list us vs  in equal_if uu____2714)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2715),uu____2716) -> Unknown
      | (uu____2717,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2718)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2721 = FStar_Const.eq_const c d  in equal_iff uu____2721
      | (FStar_Syntax_Syntax.Tm_uvar u1,FStar_Syntax_Syntax.Tm_uvar u2) ->
          let uu____2724 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____2724
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2769 =
            let uu____2774 =
              let uu____2775 = un_uinst h1  in
              uu____2775.FStar_Syntax_Syntax.n  in
            let uu____2778 =
              let uu____2779 = un_uinst h2  in
              uu____2779.FStar_Syntax_Syntax.n  in
            (uu____2774, uu____2778)  in
          (match uu____2769 with
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
                 (let uu____2791 =
                    let uu____2792 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____2792  in
                  FStar_List.mem uu____2791 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____2793 ->
               let uu____2798 = eq_tm h1 h2  in
               eq_and uu____2798 (fun uu____2800  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____2905 = FStar_List.zip bs1 bs2  in
            let uu____2968 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3005  ->
                 fun a  ->
                   match uu____3005 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3098  -> branch_matches b1 b2))
              uu____2905 uu____2968
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3102 = eq_univs u v1  in equal_if uu____3102
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) -> if q1 = q2 then eq_tm t12 t22 else Unknown
      | uu____3116 -> Unknown

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
        | (uu____3199,uu____3200) -> false  in
      let uu____3209 = b1  in
      match uu____3209 with
      | (p1,w1,t1) ->
          let uu____3243 = b2  in
          (match uu____3243 with
           | (p2,w2,t2) ->
               let uu____3277 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3277
               then
                 let uu____3278 =
                   (let uu____3281 = eq_tm t1 t2  in uu____3281 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3290 = eq_tm t11 t21  in
                             uu____3290 = Equal) w1 w2)
                    in
                 (if uu____3278 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3340)::a11,(b,uu____3343)::b1) ->
          let uu____3397 = eq_tm a b  in
          (match uu____3397 with
           | Equal  -> eq_args a11 b1
           | uu____3398 -> Unknown)
      | uu____3399 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3429) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3435,uu____3436) ->
        unrefine t2
    | uu____3477 -> t1
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3483 =
      let uu____3484 = unrefine t  in uu____3484.FStar_Syntax_Syntax.n  in
    match uu____3483 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3489) -> is_unit t1
    | uu____3494 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3500 =
      let uu____3501 = unrefine t  in uu____3501.FStar_Syntax_Syntax.n  in
    match uu____3500 with
    | FStar_Syntax_Syntax.Tm_type uu____3504 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3507) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3529) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3534,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3552 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____3558 =
      let uu____3559 = FStar_Syntax_Subst.compress e  in
      uu____3559.FStar_Syntax_Syntax.n  in
    match uu____3558 with
    | FStar_Syntax_Syntax.Tm_abs uu____3562 -> true
    | uu____3579 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3585 =
      let uu____3586 = FStar_Syntax_Subst.compress t  in
      uu____3586.FStar_Syntax_Syntax.n  in
    match uu____3585 with
    | FStar_Syntax_Syntax.Tm_arrow uu____3589 -> true
    | uu____3602 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3610) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3616,uu____3617) ->
        pre_typ t2
    | uu____3658 -> t1
  
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
      let uu____3680 =
        let uu____3681 = un_uinst typ1  in uu____3681.FStar_Syntax_Syntax.n
         in
      match uu____3680 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____3736 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____3760 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____3778,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____3785) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____3790,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3801,uu____3802,uu____3803,uu____3804,uu____3805) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____3815,uu____3816,uu____3817,uu____3818) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____3824,uu____3825,uu____3826,uu____3827,uu____3828) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3834,uu____3835) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3837,uu____3838) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3841 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____3842 -> []
    | FStar_Syntax_Syntax.Sig_main uu____3843 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____3856 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___51_3879  ->
    match uu___51_3879 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____3892 'Auu____3893 .
    ('Auu____3892 FStar_Syntax_Syntax.syntax,'Auu____3893)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____3904  ->
    match uu____3904 with | (hd1,uu____3912) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____3925 'Auu____3926 .
    ('Auu____3925 FStar_Syntax_Syntax.syntax,'Auu____3926)
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
      | uu____4017 ->
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
          let uu____4077 = FStar_Ident.range_of_lid l  in
          let uu____4078 =
            let uu____4085 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____4085  in
          uu____4078 FStar_Pervasives_Native.None uu____4077
      | uu____4089 ->
          let e =
            let uu____4101 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____4101 args  in
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
      let uu____4116 =
        let uu____4121 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____4121, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____4116
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
          let uu____4172 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____4172
          then
            let uu____4173 =
              let uu____4178 =
                let uu____4179 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____4179  in
              let uu____4180 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____4178, uu____4180)  in
            FStar_Ident.mk_ident uu____4173
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___57_4183 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___57_4183.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___57_4183.FStar_Syntax_Syntax.sort)
          }  in
        let uu____4184 = mk_field_projector_name_from_ident lid nm  in
        (uu____4184, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4195) -> ses
    | uu____4204 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____4213 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____4224 = FStar_Syntax_Unionfind.find uv  in
      match uu____4224 with
      | FStar_Pervasives_Native.Some uu____4227 ->
          let uu____4228 =
            let uu____4229 =
              let uu____4230 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____4230  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4229  in
          failwith uu____4228
      | uu____4231 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____4306 -> q1 = q2
  
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
              let uu____4351 =
                let uu___58_4352 = rc  in
                let uu____4353 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___58_4352.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____4353;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___58_4352.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____4351
           in
        match bs with
        | [] -> t
        | uu____4368 ->
            let body =
              let uu____4370 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4370  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4400 =
                   let uu____4407 =
                     let uu____4408 =
                       let uu____4425 =
                         let uu____4432 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4432 bs'  in
                       let uu____4443 = close_lopt lopt'  in
                       (uu____4425, t1, uu____4443)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4408  in
                   FStar_Syntax_Syntax.mk uu____4407  in
                 uu____4400 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4459 ->
                 let uu____4466 =
                   let uu____4473 =
                     let uu____4474 =
                       let uu____4491 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4498 = close_lopt lopt  in
                       (uu____4491, body, uu____4498)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4474  in
                   FStar_Syntax_Syntax.mk uu____4473  in
                 uu____4466 FStar_Pervasives_Native.None
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
      | uu____4548 ->
          let uu____4555 =
            let uu____4562 =
              let uu____4563 =
                let uu____4576 = FStar_Syntax_Subst.close_binders bs  in
                let uu____4583 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____4576, uu____4583)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4563  in
            FStar_Syntax_Syntax.mk uu____4562  in
          uu____4555 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____4628 =
        let uu____4629 = FStar_Syntax_Subst.compress t  in
        uu____4629.FStar_Syntax_Syntax.n  in
      match uu____4628 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____4655) ->
               let uu____4664 =
                 let uu____4665 = FStar_Syntax_Subst.compress tres  in
                 uu____4665.FStar_Syntax_Syntax.n  in
               (match uu____4664 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____4700 -> t)
           | uu____4701 -> t)
      | uu____4702 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____4719 =
        let uu____4720 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____4720 t.FStar_Syntax_Syntax.pos  in
      let uu____4721 =
        let uu____4728 =
          let uu____4729 =
            let uu____4736 =
              let uu____4739 =
                let uu____4740 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____4740]  in
              FStar_Syntax_Subst.close uu____4739 t  in
            (b, uu____4736)  in
          FStar_Syntax_Syntax.Tm_refine uu____4729  in
        FStar_Syntax_Syntax.mk uu____4728  in
      uu____4721 FStar_Pervasives_Native.None uu____4719
  
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
        let uu____4807 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____4807 with
         | (bs1,c1) ->
             let uu____4824 = is_total_comp c1  in
             if uu____4824
             then
               let uu____4835 = arrow_formals_comp (comp_result c1)  in
               (match uu____4835 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____4887;
           FStar_Syntax_Syntax.index = uu____4888;
           FStar_Syntax_Syntax.sort = k2;_},uu____4890)
        -> arrow_formals_comp k2
    | uu____4897 ->
        let uu____4898 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4898)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____4926 = arrow_formals_comp k  in
    match uu____4926 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____5008 =
            let uu___59_5009 = rc  in
            let uu____5010 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___59_5009.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____5010;
              FStar_Syntax_Syntax.residual_flags =
                (uu___59_5009.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____5008
      | uu____5019 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____5051 =
        let uu____5052 =
          let uu____5055 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____5055  in
        uu____5052.FStar_Syntax_Syntax.n  in
      match uu____5051 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____5095 = aux t2 what  in
          (match uu____5095 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____5155 -> ([], t1, abs_body_lcomp)  in
    let uu____5168 = aux t FStar_Pervasives_Native.None  in
    match uu____5168 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____5210 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____5210 with
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
                    | (FStar_Pervasives_Native.None ,uu____5371) -> def
                    | (uu____5382,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____5394) ->
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
                                          Prims.list,FStar_Syntax_Syntax.comp'
                                                       FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple3)
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____5484 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____5484 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5515 ->
            let t' = arrow binders c  in
            let uu____5525 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5525 with
             | (uvs1,t'1) ->
                 let uu____5546 =
                   let uu____5547 = FStar_Syntax_Subst.compress t'1  in
                   uu____5547.FStar_Syntax_Syntax.n  in
                 (match uu____5546 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____5590 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____5611 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____5618 -> false
  
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
      let uu____5666 =
        let uu____5667 = pre_typ t  in uu____5667.FStar_Syntax_Syntax.n  in
      match uu____5666 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____5671 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____5682 =
        let uu____5683 = pre_typ t  in uu____5683.FStar_Syntax_Syntax.n  in
      match uu____5682 with
      | FStar_Syntax_Syntax.Tm_fvar uu____5686 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____5688) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5710) ->
          is_constructed_typ t1 lid
      | uu____5715 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____5726 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____5727 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____5728 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5730) -> get_tycon t2
    | uu____5751 -> FStar_Pervasives_Native.None
  
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
    let uu____5765 =
      let uu____5766 = un_uinst t  in uu____5766.FStar_Syntax_Syntax.n  in
    match uu____5765 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____5770 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____5777 =
        let uu____5780 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____5780  in
      match uu____5777 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____5793 -> false
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
  fun uu____5809  ->
    let u =
      let uu____5815 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_5  -> FStar_Syntax_Syntax.U_unif _0_5)
        uu____5815
       in
    let uu____5832 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____5832, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____5843 = eq_tm a a'  in
      match uu____5843 with | Equal  -> true | uu____5844 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____5847 =
    let uu____5854 =
      let uu____5855 =
        let uu____5856 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____5856
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____5855  in
    FStar_Syntax_Syntax.mk uu____5854  in
  uu____5847 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____5935 =
            let uu____5938 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____5939 =
              let uu____5946 =
                let uu____5947 =
                  let uu____5962 =
                    let uu____5971 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____5978 =
                      let uu____5987 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____5987]  in
                    uu____5971 :: uu____5978  in
                  (tand, uu____5962)  in
                FStar_Syntax_Syntax.Tm_app uu____5947  in
              FStar_Syntax_Syntax.mk uu____5946  in
            uu____5939 FStar_Pervasives_Native.None uu____5938  in
          FStar_Pervasives_Native.Some uu____5935
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____6056 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____6057 =
          let uu____6064 =
            let uu____6065 =
              let uu____6080 =
                let uu____6089 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____6096 =
                  let uu____6105 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____6105]  in
                uu____6089 :: uu____6096  in
              (op_t, uu____6080)  in
            FStar_Syntax_Syntax.Tm_app uu____6065  in
          FStar_Syntax_Syntax.mk uu____6064  in
        uu____6057 FStar_Pervasives_Native.None uu____6056
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____6154 =
      let uu____6161 =
        let uu____6162 =
          let uu____6177 =
            let uu____6186 = FStar_Syntax_Syntax.as_arg phi  in [uu____6186]
             in
          (t_not, uu____6177)  in
        FStar_Syntax_Syntax.Tm_app uu____6162  in
      FStar_Syntax_Syntax.mk uu____6161  in
    uu____6154 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
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
    let uu____6371 =
      let uu____6378 =
        let uu____6379 =
          let uu____6394 =
            let uu____6403 = FStar_Syntax_Syntax.as_arg e  in [uu____6403]
             in
          (b2t_v, uu____6394)  in
        FStar_Syntax_Syntax.Tm_app uu____6379  in
      FStar_Syntax_Syntax.mk uu____6378  in
    uu____6371 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____6455 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____6456 =
        let uu____6463 =
          let uu____6464 =
            let uu____6479 =
              let uu____6488 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____6495 =
                let uu____6504 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____6504]  in
              uu____6488 :: uu____6495  in
            (teq, uu____6479)  in
          FStar_Syntax_Syntax.Tm_app uu____6464  in
        FStar_Syntax_Syntax.mk uu____6463  in
      uu____6456 FStar_Pervasives_Native.None uu____6455
  
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
          let uu____6563 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____6564 =
            let uu____6571 =
              let uu____6572 =
                let uu____6587 =
                  let uu____6596 = FStar_Syntax_Syntax.iarg t  in
                  let uu____6603 =
                    let uu____6612 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____6619 =
                      let uu____6628 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____6628]  in
                    uu____6612 :: uu____6619  in
                  uu____6596 :: uu____6603  in
                (eq_inst, uu____6587)  in
              FStar_Syntax_Syntax.Tm_app uu____6572  in
            FStar_Syntax_Syntax.mk uu____6571  in
          uu____6564 FStar_Pervasives_Native.None uu____6563
  
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
        let uu____6695 =
          let uu____6702 =
            let uu____6703 =
              let uu____6718 =
                let uu____6727 = FStar_Syntax_Syntax.iarg t  in
                let uu____6734 =
                  let uu____6743 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____6750 =
                    let uu____6759 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____6759]  in
                  uu____6743 :: uu____6750  in
                uu____6727 :: uu____6734  in
              (t_has_type1, uu____6718)  in
            FStar_Syntax_Syntax.Tm_app uu____6703  in
          FStar_Syntax_Syntax.mk uu____6702  in
        uu____6695 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____6826 =
          let uu____6833 =
            let uu____6834 =
              let uu____6849 =
                let uu____6858 = FStar_Syntax_Syntax.iarg t  in
                let uu____6865 =
                  let uu____6874 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____6874]  in
                uu____6858 :: uu____6865  in
              (t_with_type1, uu____6849)  in
            FStar_Syntax_Syntax.Tm_app uu____6834  in
          FStar_Syntax_Syntax.mk uu____6833  in
        uu____6826 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu____6914 =
    let uu____6921 =
      let uu____6922 =
        let uu____6929 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____6929, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____6922  in
    FStar_Syntax_Syntax.mk uu____6921  in
  uu____6914 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
  
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.lcomp) =
  fun c0  ->
    let uu____6942 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____6955 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____6966 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____6942 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____6987  -> c0)
  
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
        let uu____7065 =
          let uu____7072 =
            let uu____7073 =
              let uu____7088 =
                let uu____7097 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____7104 =
                  let uu____7113 =
                    let uu____7120 =
                      let uu____7121 =
                        let uu____7122 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____7122]  in
                      abs uu____7121 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____7120  in
                  [uu____7113]  in
                uu____7097 :: uu____7104  in
              (fa, uu____7088)  in
            FStar_Syntax_Syntax.Tm_app uu____7073  in
          FStar_Syntax_Syntax.mk uu____7072  in
        uu____7065 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____7227 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____7227
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____7238 -> true
    | uu____7239 -> false
  
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
          let uu____7284 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____7284, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____7312 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____7312, FStar_Pervasives_Native.None, t2)  in
        let uu____7325 =
          let uu____7326 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____7326  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____7325
  
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
      let uu____7400 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7403 =
        let uu____7412 = FStar_Syntax_Syntax.as_arg p  in [uu____7412]  in
      mk_app uu____7400 uu____7403
  
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
      let uu____7444 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7447 =
        let uu____7456 = FStar_Syntax_Syntax.as_arg p  in [uu____7456]  in
      mk_app uu____7444 uu____7447
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7482 = head_and_args t  in
    match uu____7482 with
    | (head1,args) ->
        let uu____7515 =
          let uu____7528 =
            let uu____7529 = un_uinst head1  in
            uu____7529.FStar_Syntax_Syntax.n  in
          (uu____7528, args)  in
        (match uu____7515 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____7544)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____7594 =
                    let uu____7599 =
                      let uu____7600 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____7600]  in
                    FStar_Syntax_Subst.open_term uu____7599 p  in
                  (match uu____7594 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____7639 -> failwith "impossible"  in
                       let uu____7644 =
                         let uu____7645 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____7645
                          in
                       if uu____7644
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____7651 -> FStar_Pervasives_Native.None)
         | uu____7652 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7678 = head_and_args t  in
    match uu____7678 with
    | (head1,args) ->
        let uu____7717 =
          let uu____7730 =
            let uu____7731 = FStar_Syntax_Subst.compress head1  in
            uu____7731.FStar_Syntax_Syntax.n  in
          (uu____7730, args)  in
        (match uu____7717 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____7751;
               FStar_Syntax_Syntax.vars = uu____7752;_},u::[]),(t1,uu____7755)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____7792 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7824 = head_and_args t  in
    match uu____7824 with
    | (head1,args) ->
        let uu____7863 =
          let uu____7876 =
            let uu____7877 = FStar_Syntax_Subst.compress head1  in
            uu____7877.FStar_Syntax_Syntax.n  in
          (uu____7876, args)  in
        (match uu____7863 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____7897;
               FStar_Syntax_Syntax.vars = uu____7898;_},u::[]),(t1,uu____7901)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____7938 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____7962 = let uu____7975 = unmeta t  in head_and_args uu____7975
       in
    match uu____7962 with
    | (head1,uu____7977) ->
        let uu____7994 =
          let uu____7995 = un_uinst head1  in
          uu____7995.FStar_Syntax_Syntax.n  in
        (match uu____7994 with
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
         | uu____7999 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8017 =
      let uu____8028 =
        let uu____8029 = FStar_Syntax_Subst.compress t  in
        uu____8029.FStar_Syntax_Syntax.n  in
      match uu____8028 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____8132 =
            let uu____8141 =
              let uu____8142 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____8142  in
            (b, uu____8141)  in
          FStar_Pervasives_Native.Some uu____8132
      | uu____8155 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____8017
      (fun uu____8187  ->
         match uu____8187 with
         | (b,c) ->
             let uu____8216 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____8216 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____8263 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____8290 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8290
  
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
    match projectee with | QAll _0 -> true | uu____8338 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____8376 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____8412 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____8449) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____8461) ->
          unmeta_monadic t
      | uu____8474 -> f2  in
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
      let aux f2 uu____8558 =
        match uu____8558 with
        | (lid,arity) ->
            let uu____8567 =
              let uu____8580 = unmeta_monadic f2  in head_and_args uu____8580
               in
            (match uu____8567 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____8602 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____8602
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____8671 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____8671)
      | uu____8682 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____8737 = head_and_args t1  in
        match uu____8737 with
        | (t2,args) ->
            let uu____8778 = un_uinst t2  in
            let uu____8779 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____8810  ->
                      match uu____8810 with
                      | (t3,imp) ->
                          let uu____8821 = unascribe t3  in (uu____8821, imp)))
               in
            (uu____8778, uu____8779)
         in
      let rec aux qopt out t1 =
        let uu____8862 = let uu____8883 = flat t1  in (qopt, uu____8883)  in
        match uu____8862 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____8918;
                 FStar_Syntax_Syntax.vars = uu____8919;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____8922);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____8923;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____8924;_},uu____8925)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____9002;
                 FStar_Syntax_Syntax.vars = uu____9003;_},uu____9004::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____9007);
                  FStar_Syntax_Syntax.pos = uu____9008;
                  FStar_Syntax_Syntax.vars = uu____9009;_},uu____9010)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9098;
               FStar_Syntax_Syntax.vars = uu____9099;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____9102);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____9103;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____9104;_},uu____9105)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9176 =
              let uu____9179 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9179  in
            aux uu____9176 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9185;
               FStar_Syntax_Syntax.vars = uu____9186;_},uu____9187::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____9190);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____9191;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____9192;_},uu____9193)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9276 =
              let uu____9279 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9279  in
            aux uu____9276 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____9285) ->
            let bs = FStar_List.rev out  in
            let uu____9327 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____9327 with
             | (bs1,t2) ->
                 let uu____9336 = patterns t2  in
                 (match uu____9336 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____9378 -> FStar_Pervasives_Native.None  in
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
      let uu____9450 = un_squash t  in
      FStar_Util.bind_opt uu____9450
        (fun t1  ->
           let uu____9460 = head_and_args' t1  in
           match uu____9460 with
           | (hd1,args) ->
               let uu____9493 =
                 let uu____9498 =
                   let uu____9499 = un_uinst hd1  in
                   uu____9499.FStar_Syntax_Syntax.n  in
                 (uu____9498, (FStar_List.length args))  in
               (match uu____9493 with
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
                | uu____9518 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____9547 = un_squash t  in
      FStar_Util.bind_opt uu____9547
        (fun t1  ->
           let uu____9556 = arrow_one t1  in
           match uu____9556 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____9571 =
                 let uu____9572 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____9572  in
               if uu____9571
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____9579 = comp_to_comp_typ_nouniv c  in
                    uu____9579.FStar_Syntax_Syntax.result_typ  in
                  let uu____9580 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____9580
                  then
                    let uu____9583 = patterns q  in
                    match uu____9583 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____9635 =
                       let uu____9636 =
                         let uu____9641 =
                           let uu____9642 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____9649 =
                             let uu____9658 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____9658]  in
                           uu____9642 :: uu____9649  in
                         (FStar_Parser_Const.imp_lid, uu____9641)  in
                       BaseConn uu____9636  in
                     FStar_Pervasives_Native.Some uu____9635))
           | uu____9683 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____9691 = un_squash t  in
      FStar_Util.bind_opt uu____9691
        (fun t1  ->
           let uu____9716 = head_and_args' t1  in
           match uu____9716 with
           | (hd1,args) ->
               let uu____9749 =
                 let uu____9762 =
                   let uu____9763 = un_uinst hd1  in
                   uu____9763.FStar_Syntax_Syntax.n  in
                 (uu____9762, args)  in
               (match uu____9749 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____9778)::(a2,uu____9780)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____9815 =
                      let uu____9816 = FStar_Syntax_Subst.compress a2  in
                      uu____9816.FStar_Syntax_Syntax.n  in
                    (match uu____9815 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____9823) ->
                         let uu____9850 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____9850 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____9889 -> failwith "impossible"  in
                              let uu____9894 = patterns q1  in
                              (match uu____9894 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____9945 -> FStar_Pervasives_Native.None)
                | uu____9946 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____9967 = destruct_sq_forall phi  in
          (match uu____9967 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____9981 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____9987 = destruct_sq_exists phi  in
          (match uu____9987 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____10001 -> f1)
      | uu____10004 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____10008 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____10008
      (fun uu____10013  ->
         let uu____10014 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____10014
           (fun uu____10019  ->
              let uu____10020 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____10020
                (fun uu____10025  ->
                   let uu____10026 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____10026
                     (fun uu____10031  ->
                        let uu____10032 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____10032
                          (fun uu____10036  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____10048 =
      let uu____10049 = FStar_Syntax_Subst.compress t  in
      uu____10049.FStar_Syntax_Syntax.n  in
    match uu____10048 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____10056) ->
        let uu____10083 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____10083 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____10109 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____10109
             then
               let uu____10112 =
                 let uu____10121 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____10121]  in
               mk_app t uu____10112
             else e1)
    | uu____10141 ->
        let uu____10142 =
          let uu____10151 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____10151]  in
        mk_app t uu____10142
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____10186 =
            let uu____10191 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.Delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____10191  in
          let uu____10192 =
            let uu____10193 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____10193  in
          let uu____10196 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____10186 a.FStar_Syntax_Syntax.action_univs uu____10192
            FStar_Parser_Const.effect_Tot_lid uu____10196 [] pos
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
    let uu____10219 =
      let uu____10226 =
        let uu____10227 =
          let uu____10242 =
            let uu____10251 = FStar_Syntax_Syntax.as_arg t  in [uu____10251]
             in
          (reify_, uu____10242)  in
        FStar_Syntax_Syntax.Tm_app uu____10227  in
      FStar_Syntax_Syntax.mk uu____10226  in
    uu____10219 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10289 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____10315 = unfold_lazy i  in delta_qualifier uu____10315
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____10317 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____10318 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____10319 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____10342 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____10343 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____10344 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____10351 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____10352 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____10366) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____10371;
           FStar_Syntax_Syntax.index = uu____10372;
           FStar_Syntax_Syntax.sort = t2;_},uu____10374)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____10382) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____10388,uu____10389) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____10431) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____10452,t2,uu____10454) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____10475,t2) -> delta_qualifier t2
  
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
    let uu____10505 = delta_qualifier t  in incr_delta_depth uu____10505
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____10511 =
      let uu____10512 = FStar_Syntax_Subst.compress t  in
      uu____10512.FStar_Syntax_Syntax.n  in
    match uu____10511 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____10515 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____10529 =
      let uu____10542 = unmeta e  in head_and_args uu____10542  in
    match uu____10529 with
    | (head1,args) ->
        let uu____10565 =
          let uu____10578 =
            let uu____10579 = un_uinst head1  in
            uu____10579.FStar_Syntax_Syntax.n  in
          (uu____10578, args)  in
        (match uu____10565 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10595) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____10615::(hd1,uu____10617)::(tl1,uu____10619)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____10666 =
               let uu____10669 =
                 let uu____10672 = list_elements tl1  in
                 FStar_Util.must uu____10672  in
               hd1 :: uu____10669  in
             FStar_Pervasives_Native.Some uu____10666
         | uu____10681 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____10703 .
    ('Auu____10703 -> 'Auu____10703) ->
      'Auu____10703 Prims.list -> 'Auu____10703 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____10728 = f a  in [uu____10728]
      | x::xs -> let uu____10733 = apply_last f xs  in x :: uu____10733
  
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
          let uu____10779 =
            let uu____10786 =
              let uu____10787 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____10787  in
            FStar_Syntax_Syntax.mk uu____10786  in
          uu____10779 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____10804 =
            let uu____10809 =
              let uu____10810 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____10810
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____10809 args  in
          uu____10804 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____10826 =
            let uu____10831 =
              let uu____10832 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____10832
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____10831 args  in
          uu____10826 FStar_Pervasives_Native.None pos  in
        let uu____10835 =
          let uu____10836 =
            let uu____10837 = FStar_Syntax_Syntax.iarg typ  in [uu____10837]
             in
          nil uu____10836 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____10865 =
                 let uu____10866 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____10873 =
                   let uu____10882 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____10889 =
                     let uu____10898 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____10898]  in
                   uu____10882 :: uu____10889  in
                 uu____10866 :: uu____10873  in
               cons1 uu____10865 t.FStar_Syntax_Syntax.pos) l uu____10835
  
let (uvar_from_id :
  Prims.int ->
    (FStar_Syntax_Syntax.binding Prims.list,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                              FStar_Pervasives_Native.tuple2
                                              Prims.list,FStar_Syntax_Syntax.term'
                                                           FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun id1  ->
    fun uu____10956  ->
      match uu____10956 with
      | (gamma,bs,t) ->
          let ctx_u =
            let uu____10999 = FStar_Syntax_Unionfind.from_id id1  in
            {
              FStar_Syntax_Syntax.ctx_uvar_head = uu____10999;
              FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
              FStar_Syntax_Syntax.ctx_uvar_binders = bs;
              FStar_Syntax_Syntax.ctx_uvar_typ = t;
              FStar_Syntax_Syntax.ctx_uvar_reason = "";
              FStar_Syntax_Syntax.ctx_uvar_should_check = true;
              FStar_Syntax_Syntax.ctx_uvar_range = FStar_Range.dummyRange
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        | uu____11073 -> false
  
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
          | uu____11180 -> false
  
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
        | uu____11335 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____11369 = FStar_ST.op_Bang debug_term_eq  in
          if uu____11369
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
        let t11 = let uu____11557 = unmeta_safe t1  in canon_app uu____11557
           in
        let t21 = let uu____11563 = unmeta_safe t2  in canon_app uu____11563
           in
        let uu____11566 =
          let uu____11571 =
            let uu____11572 =
              let uu____11575 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____11575  in
            uu____11572.FStar_Syntax_Syntax.n  in
          let uu____11576 =
            let uu____11577 =
              let uu____11580 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____11580  in
            uu____11577.FStar_Syntax_Syntax.n  in
          (uu____11571, uu____11576)  in
        match uu____11566 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____11581,uu____11582) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____11589,FStar_Syntax_Syntax.Tm_uinst uu____11590) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____11597,uu____11598) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____11623,FStar_Syntax_Syntax.Tm_delayed uu____11624) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____11649,uu____11650) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____11677,FStar_Syntax_Syntax.Tm_ascribed uu____11678) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____11711 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____11711
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____11714 = FStar_Const.eq_const c1 c2  in
            check "const" uu____11714
        | (FStar_Syntax_Syntax.Tm_type
           uu____11715,FStar_Syntax_Syntax.Tm_type uu____11716) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____11765 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____11765) &&
              (let uu____11771 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____11771)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____11810 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____11810) &&
              (let uu____11816 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____11816)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____11830 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____11830)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____11877 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____11877) &&
              (let uu____11879 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____11879)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____11964 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____11964) &&
              (let uu____11966 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____11966)
        | (FStar_Syntax_Syntax.Tm_lazy uu____11981,uu____11982) ->
            let uu____11983 =
              let uu____11984 = unlazy t11  in
              term_eq_dbg dbg uu____11984 t21  in
            check "lazy_l" uu____11983
        | (uu____11985,FStar_Syntax_Syntax.Tm_lazy uu____11986) ->
            let uu____11987 =
              let uu____11988 = unlazy t21  in
              term_eq_dbg dbg t11 uu____11988  in
            check "lazy_r" uu____11987
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____12024 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____12024))
              &&
              (let uu____12026 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____12026)
        | (FStar_Syntax_Syntax.Tm_uvar u1,FStar_Syntax_Syntax.Tm_uvar u2) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (check "tm_quoted qi" (qi1 = qi2)) &&
              (let uu____12052 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____12052)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____12079 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____12079) &&
                   (let uu____12081 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____12081)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____12098 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____12098) &&
                    (let uu____12100 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____12100))
                   &&
                   (let uu____12102 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____12102)
             | uu____12103 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____12108) -> fail "unk"
        | (uu____12109,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____12110,uu____12111) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____12112,uu____12113) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____12114,uu____12115) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____12116,uu____12117) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____12118,uu____12119) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____12120,uu____12121) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____12138,uu____12139) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____12152,uu____12153) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____12160,uu____12161) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____12176,uu____12177) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____12200,uu____12201) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____12214,uu____12215) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____12216,uu____12217) ->
            fail "bottom"
        | (uu____12224,FStar_Syntax_Syntax.Tm_bvar uu____12225) ->
            fail "bottom"
        | (uu____12226,FStar_Syntax_Syntax.Tm_name uu____12227) ->
            fail "bottom"
        | (uu____12228,FStar_Syntax_Syntax.Tm_fvar uu____12229) ->
            fail "bottom"
        | (uu____12230,FStar_Syntax_Syntax.Tm_constant uu____12231) ->
            fail "bottom"
        | (uu____12232,FStar_Syntax_Syntax.Tm_type uu____12233) ->
            fail "bottom"
        | (uu____12234,FStar_Syntax_Syntax.Tm_abs uu____12235) ->
            fail "bottom"
        | (uu____12252,FStar_Syntax_Syntax.Tm_arrow uu____12253) ->
            fail "bottom"
        | (uu____12266,FStar_Syntax_Syntax.Tm_refine uu____12267) ->
            fail "bottom"
        | (uu____12274,FStar_Syntax_Syntax.Tm_app uu____12275) ->
            fail "bottom"
        | (uu____12290,FStar_Syntax_Syntax.Tm_match uu____12291) ->
            fail "bottom"
        | (uu____12314,FStar_Syntax_Syntax.Tm_let uu____12315) ->
            fail "bottom"
        | (uu____12328,FStar_Syntax_Syntax.Tm_uvar uu____12329) ->
            fail "bottom"
        | (uu____12330,FStar_Syntax_Syntax.Tm_meta uu____12331) ->
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
               let uu____12358 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____12358)
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
               let uu____12379 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____12379)
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
        ((let uu____12399 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____12399) &&
           (let uu____12401 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____12401))
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
    fun uu____12406  ->
      fun uu____12407  ->
        match (uu____12406, uu____12407) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____12532 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____12532) &&
               (let uu____12534 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____12534))
              &&
              (let uu____12536 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____12551 -> false  in
               check "branch when" uu____12536)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____12565 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____12565) &&
           (let uu____12571 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____12571))
          &&
          (let uu____12573 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____12573)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____12585 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____12585 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____12638 ->
        let uu____12663 =
          let uu____12664 = FStar_Syntax_Subst.compress t  in
          sizeof uu____12664  in
        (Prims.parse_int "1") + uu____12663
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____12666 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____12666
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____12668 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____12668
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____12675 = sizeof t1  in (FStar_List.length us) + uu____12675
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____12678) ->
        let uu____12699 = sizeof t1  in
        let uu____12700 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____12711  ->
                 match uu____12711 with
                 | (bv,uu____12717) ->
                     let uu____12718 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____12718) (Prims.parse_int "0") bs
           in
        uu____12699 + uu____12700
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____12741 = sizeof hd1  in
        let uu____12742 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____12753  ->
                 match uu____12753 with
                 | (arg,uu____12759) ->
                     let uu____12760 = sizeof arg  in acc + uu____12760)
            (Prims.parse_int "0") args
           in
        uu____12741 + uu____12742
    | uu____12761 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____12772 =
        let uu____12773 = un_uinst t  in uu____12773.FStar_Syntax_Syntax.n
         in
      match uu____12772 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____12777 -> false
  
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
        let uu____12818 = FStar_Options.set_options t s  in
        match uu____12818 with
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
          ((let uu____12826 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____12826 (fun a237  -> ()));
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
    | FStar_Syntax_Syntax.Tm_delayed uu____12852 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____12880 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____12883 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____12884 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____12885 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____12894) ->
        let uu____12915 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____12915 with
         | (bs1,t2) ->
             let uu____12924 =
               FStar_List.collect
                 (fun uu____12934  ->
                    match uu____12934 with
                    | (b,uu____12942) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____12943 = unbound_variables t2  in
             FStar_List.append uu____12924 uu____12943)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____12964 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____12964 with
         | (bs1,c1) ->
             let uu____12973 =
               FStar_List.collect
                 (fun uu____12983  ->
                    match uu____12983 with
                    | (b,uu____12991) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____12992 = unbound_variables_comp c1  in
             FStar_List.append uu____12973 uu____12992)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____13001 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____13001 with
         | (bs,t2) ->
             let uu____13018 =
               FStar_List.collect
                 (fun uu____13028  ->
                    match uu____13028 with
                    | (b1,uu____13036) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____13037 = unbound_variables t2  in
             FStar_List.append uu____13018 uu____13037)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____13062 =
          FStar_List.collect
            (fun uu____13074  ->
               match uu____13074 with
               | (x,uu____13084) -> unbound_variables x) args
           in
        let uu____13089 = unbound_variables t1  in
        FStar_List.append uu____13062 uu____13089
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____13130 = unbound_variables t1  in
        let uu____13133 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____13148 = FStar_Syntax_Subst.open_branch br  in
                  match uu____13148 with
                  | (p,wopt,t2) ->
                      let uu____13170 = unbound_variables t2  in
                      let uu____13173 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____13170 uu____13173))
           in
        FStar_List.append uu____13130 uu____13133
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____13187) ->
        let uu____13228 = unbound_variables t1  in
        let uu____13231 =
          let uu____13234 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____13265 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____13234 uu____13265  in
        FStar_List.append uu____13228 uu____13231
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____13303 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____13306 =
          let uu____13309 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____13312 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____13317 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____13319 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____13319 with
                 | (uu____13334,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____13309 uu____13312  in
        FStar_List.append uu____13303 uu____13306
    | FStar_Syntax_Syntax.Tm_let ((uu____13336,lbs),t1) ->
        let uu____13353 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____13353 with
         | (lbs1,t2) ->
             let uu____13368 = unbound_variables t2  in
             let uu____13371 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____13378 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____13381 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____13378 uu____13381) lbs1
                in
             FStar_List.append uu____13368 uu____13371)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____13398 = unbound_variables t1  in
        let uu____13401 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____13434  ->
                      match uu____13434 with
                      | (a,uu____13444) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____13449,uu____13450,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____13456,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____13462 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____13469 -> []
          | FStar_Syntax_Syntax.Meta_named uu____13470 -> []  in
        FStar_List.append uu____13398 uu____13401

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____13477) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____13487) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____13497 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____13500 =
          FStar_List.collect
            (fun uu____13512  ->
               match uu____13512 with
               | (a,uu____13522) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____13497 uu____13500
