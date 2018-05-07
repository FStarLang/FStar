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
      let uu___78_1279 = c  in
      let uu____1280 =
        let uu____1281 =
          let uu___79_1282 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___79_1282.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___79_1282.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___79_1282.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___79_1282.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1281  in
      {
        FStar_Syntax_Syntax.n = uu____1280;
        FStar_Syntax_Syntax.pos = (uu___78_1279.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___78_1279.FStar_Syntax_Syntax.vars)
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
              let uu___80_1327 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___80_1327.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___80_1327.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___80_1327.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___80_1327.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___81_1328 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___81_1328.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___81_1328.FStar_Syntax_Syntax.vars)
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
            (fun uu___66_1408  ->
               match uu___66_1408 with
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
            (fun uu___67_1418  ->
               match uu___67_1418 with
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
            (fun uu___68_1428  ->
               match uu___68_1428 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1429 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___69_1442  ->
            match uu___69_1442 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1443 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___70_1452  ->
            match uu___70_1452 with
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
                (fun uu___71_1499  ->
                   match uu___71_1499 with
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
            (fun uu___72_1528  ->
               match uu___72_1528 with
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
    | uu____1668 -> (t1, [])
  
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
        let uu____1735 = head_and_args' head1  in
        (match uu____1735 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1792 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1814) ->
        FStar_Syntax_Subst.compress t2
    | uu____1819 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1825 =
      let uu____1826 = FStar_Syntax_Subst.compress t  in
      uu____1826.FStar_Syntax_Syntax.n  in
    match uu____1825 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1829,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1851)::uu____1852 ->
                  let pats' = unmeta pats  in
                  let uu____1896 = head_and_args pats'  in
                  (match uu____1896 with
                   | (head1,uu____1912) ->
                       let uu____1933 =
                         let uu____1934 = un_uinst head1  in
                         uu____1934.FStar_Syntax_Syntax.n  in
                       (match uu____1933 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1938 -> false))
              | uu____1939 -> false)
         | uu____1948 -> false)
    | uu____1949 -> false
  
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
                (fun uu___73_1963  ->
                   match uu___73_1963 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1964 -> false)))
    | uu____1965 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1980) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1990) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2018 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2027 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___82_2039 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___82_2039.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___82_2039.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___82_2039.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___82_2039.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___74_2052  ->
            match uu___74_2052 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2053 -> false))
  
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
    | uu____2073 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2081,uu____2082) ->
        unascribe e2
    | uu____2123 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2175,uu____2176) ->
          ascribe t' k
      | uu____2217 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2243 =
      let uu____2252 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2252  in
    uu____2243 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2311 =
      let uu____2312 = FStar_Syntax_Subst.compress t  in
      uu____2312.FStar_Syntax_Syntax.n  in
    match uu____2311 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2316 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2316
    | uu____2317 -> t
  
let rec unlazy_as_t :
  'Auu____2324 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2324
  =
  fun k  ->
    fun t  ->
      let uu____2335 =
        let uu____2336 = FStar_Syntax_Subst.compress t  in
        uu____2336.FStar_Syntax_Syntax.n  in
      match uu____2335 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.typ = uu____2341;
            FStar_Syntax_Syntax.rng = uu____2342;_}
          when k = k' -> FStar_Dyn.undyn v1
      | uu____2345 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2384 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2384;
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
    let uu____2396 =
      let uu____2409 = unascribe t  in head_and_args' uu____2409  in
    match uu____2396 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown [@@deriving show]
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2435 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2441 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2447 -> false
  
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
      let equal_if uu___75_2523 = if uu___75_2523 then Equal else Unknown  in
      let equal_iff uu___76_2530 = if uu___76_2530 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2548 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2560) -> NotEqual
        | (uu____2561,NotEqual ) -> NotEqual
        | (Unknown ,uu____2562) -> Unknown
        | (uu____2563,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____2609 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2609
        then
          let uu____2611 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2669  ->
                    match uu____2669 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2695 = eq_tm a1 a2  in
                        eq_inj acc uu____2695) Equal) uu____2611
        else NotEqual  in
      let uu____2697 =
        let uu____2702 =
          let uu____2703 = unmeta t11  in uu____2703.FStar_Syntax_Syntax.n
           in
        let uu____2706 =
          let uu____2707 = unmeta t21  in uu____2707.FStar_Syntax_Syntax.n
           in
        (uu____2702, uu____2706)  in
      match uu____2697 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2712,uu____2713) ->
          let uu____2714 = unlazy t11  in eq_tm uu____2714 t21
      | (uu____2715,FStar_Syntax_Syntax.Tm_lazy uu____2716) ->
          let uu____2717 = unlazy t21  in eq_tm t11 uu____2717
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
            (let uu____2735 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2735)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2748 = eq_tm f g  in
          eq_and uu____2748
            (fun uu____2751  ->
               let uu____2752 = eq_univs_list us vs  in equal_if uu____2752)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2753),uu____2754) -> Unknown
      | (uu____2755,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2756)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2759 = FStar_Const.eq_const c d  in equal_iff uu____2759
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____2761)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____2763))) ->
          let uu____2804 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____2804
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2849 =
            let uu____2854 =
              let uu____2855 = un_uinst h1  in
              uu____2855.FStar_Syntax_Syntax.n  in
            let uu____2858 =
              let uu____2859 = un_uinst h2  in
              uu____2859.FStar_Syntax_Syntax.n  in
            (uu____2854, uu____2858)  in
          (match uu____2849 with
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
                 (let uu____2871 =
                    let uu____2872 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____2872  in
                  FStar_List.mem uu____2871 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____2873 ->
               let uu____2878 = eq_tm h1 h2  in
               eq_and uu____2878 (fun uu____2880  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____2985 = FStar_List.zip bs1 bs2  in
            let uu____3048 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3085  ->
                 fun a  ->
                   match uu____3085 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3178  -> branch_matches b1 b2))
              uu____2985 uu____3048
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3182 = eq_univs u v1  in equal_if uu____3182
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) -> if q1 = q2 then eq_tm t12 t22 else Unknown
      | uu____3196 -> Unknown

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
        | (uu____3279,uu____3280) -> false  in
      let uu____3289 = b1  in
      match uu____3289 with
      | (p1,w1,t1) ->
          let uu____3323 = b2  in
          (match uu____3323 with
           | (p2,w2,t2) ->
               let uu____3357 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3357
               then
                 let uu____3358 =
                   (let uu____3361 = eq_tm t1 t2  in uu____3361 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3370 = eq_tm t11 t21  in
                             uu____3370 = Equal) w1 w2)
                    in
                 (if uu____3358 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3420)::a11,(b,uu____3423)::b1) ->
          let uu____3477 = eq_tm a b  in
          (match uu____3477 with
           | Equal  -> eq_args a11 b1
           | uu____3478 -> Unknown)
      | uu____3479 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3509) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3515,uu____3516) ->
        unrefine t2
    | uu____3557 -> t1
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3563 =
      let uu____3564 = unrefine t  in uu____3564.FStar_Syntax_Syntax.n  in
    match uu____3563 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3569) -> is_unit t1
    | uu____3574 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3580 =
      let uu____3581 = unrefine t  in uu____3581.FStar_Syntax_Syntax.n  in
    match uu____3580 with
    | FStar_Syntax_Syntax.Tm_type uu____3584 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3587) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3609) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3614,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3632 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____3638 =
      let uu____3639 = FStar_Syntax_Subst.compress e  in
      uu____3639.FStar_Syntax_Syntax.n  in
    match uu____3638 with
    | FStar_Syntax_Syntax.Tm_abs uu____3642 -> true
    | uu____3659 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3665 =
      let uu____3666 = FStar_Syntax_Subst.compress t  in
      uu____3666.FStar_Syntax_Syntax.n  in
    match uu____3665 with
    | FStar_Syntax_Syntax.Tm_arrow uu____3669 -> true
    | uu____3682 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3690) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3696,uu____3697) ->
        pre_typ t2
    | uu____3738 -> t1
  
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
      let uu____3760 =
        let uu____3761 = un_uinst typ1  in uu____3761.FStar_Syntax_Syntax.n
         in
      match uu____3760 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____3816 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____3840 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____3858,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____3865) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____3870,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3881,uu____3882,uu____3883,uu____3884,uu____3885) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____3895,uu____3896,uu____3897,uu____3898) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____3904,uu____3905,uu____3906,uu____3907,uu____3908) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3914,uu____3915) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3917,uu____3918) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3921 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____3922 -> []
    | FStar_Syntax_Syntax.Sig_main uu____3923 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____3936 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___77_3959  ->
    match uu___77_3959 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____3972 'Auu____3973 .
    ('Auu____3972 FStar_Syntax_Syntax.syntax,'Auu____3973)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____3984  ->
    match uu____3984 with | (hd1,uu____3992) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____4005 'Auu____4006 .
    ('Auu____4005 FStar_Syntax_Syntax.syntax,'Auu____4006)
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
      | uu____4097 ->
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
          let uu____4157 = FStar_Ident.range_of_lid l  in
          let uu____4158 =
            let uu____4167 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____4167  in
          uu____4158 FStar_Pervasives_Native.None uu____4157
      | uu____4175 ->
          let e =
            let uu____4187 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____4187 args  in
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
      let uu____4202 =
        let uu____4207 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____4207, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____4202
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
          let uu____4258 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____4258
          then
            let uu____4259 =
              let uu____4264 =
                let uu____4265 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____4265  in
              let uu____4266 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____4264, uu____4266)  in
            FStar_Ident.mk_ident uu____4259
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___83_4269 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___83_4269.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___83_4269.FStar_Syntax_Syntax.sort)
          }  in
        let uu____4270 = mk_field_projector_name_from_ident lid nm  in
        (uu____4270, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4281) -> ses
    | uu____4290 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____4299 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____4310 = FStar_Syntax_Unionfind.find uv  in
      match uu____4310 with
      | FStar_Pervasives_Native.Some uu____4313 ->
          let uu____4314 =
            let uu____4315 =
              let uu____4316 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____4316  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4315  in
          failwith uu____4314
      | uu____4317 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____4392 -> q1 = q2
  
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
              let uu____4437 =
                let uu___84_4438 = rc  in
                let uu____4439 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___84_4438.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____4439;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___84_4438.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____4437
           in
        match bs with
        | [] -> t
        | uu____4454 ->
            let body =
              let uu____4456 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4456  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4486 =
                   let uu____4493 =
                     let uu____4494 =
                       let uu____4511 =
                         let uu____4518 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4518 bs'  in
                       let uu____4529 = close_lopt lopt'  in
                       (uu____4511, t1, uu____4529)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4494  in
                   FStar_Syntax_Syntax.mk uu____4493  in
                 uu____4486 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4545 ->
                 let uu____4552 =
                   let uu____4559 =
                     let uu____4560 =
                       let uu____4577 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4584 = close_lopt lopt  in
                       (uu____4577, body, uu____4584)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4560  in
                   FStar_Syntax_Syntax.mk uu____4559  in
                 uu____4552 FStar_Pervasives_Native.None
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
      | uu____4634 ->
          let uu____4641 =
            let uu____4648 =
              let uu____4649 =
                let uu____4662 = FStar_Syntax_Subst.close_binders bs  in
                let uu____4669 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____4662, uu____4669)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4649  in
            FStar_Syntax_Syntax.mk uu____4648  in
          uu____4641 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____4714 =
        let uu____4715 = FStar_Syntax_Subst.compress t  in
        uu____4715.FStar_Syntax_Syntax.n  in
      match uu____4714 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____4741) ->
               let uu____4750 =
                 let uu____4751 = FStar_Syntax_Subst.compress tres  in
                 uu____4751.FStar_Syntax_Syntax.n  in
               (match uu____4750 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____4786 -> t)
           | uu____4787 -> t)
      | uu____4788 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____4805 =
        let uu____4806 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____4806 t.FStar_Syntax_Syntax.pos  in
      let uu____4807 =
        let uu____4814 =
          let uu____4815 =
            let uu____4822 =
              let uu____4825 =
                let uu____4826 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____4826]  in
              FStar_Syntax_Subst.close uu____4825 t  in
            (b, uu____4822)  in
          FStar_Syntax_Syntax.Tm_refine uu____4815  in
        FStar_Syntax_Syntax.mk uu____4814  in
      uu____4807 FStar_Pervasives_Native.None uu____4805
  
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
        let uu____4893 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____4893 with
         | (bs1,c1) ->
             let uu____4910 = is_total_comp c1  in
             if uu____4910
             then
               let uu____4921 = arrow_formals_comp (comp_result c1)  in
               (match uu____4921 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____4973;
           FStar_Syntax_Syntax.index = uu____4974;
           FStar_Syntax_Syntax.sort = k2;_},uu____4976)
        -> arrow_formals_comp k2
    | uu____4983 ->
        let uu____4984 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4984)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____5012 = arrow_formals_comp k  in
    match uu____5012 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____5094 =
            let uu___85_5095 = rc  in
            let uu____5096 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___85_5095.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____5096;
              FStar_Syntax_Syntax.residual_flags =
                (uu___85_5095.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____5094
      | uu____5105 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____5137 =
        let uu____5138 =
          let uu____5141 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____5141  in
        uu____5138.FStar_Syntax_Syntax.n  in
      match uu____5137 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____5181 = aux t2 what  in
          (match uu____5181 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____5241 -> ([], t1, abs_body_lcomp)  in
    let uu____5254 = aux t FStar_Pervasives_Native.None  in
    match uu____5254 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____5296 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____5296 with
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
                    | (FStar_Pervasives_Native.None ,uu____5457) -> def
                    | (uu____5468,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____5480) ->
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
            let uu____5566 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____5566 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5595 ->
            let t' = arrow binders c  in
            let uu____5605 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5605 with
             | (uvs1,t'1) ->
                 let uu____5624 =
                   let uu____5625 = FStar_Syntax_Subst.compress t'1  in
                   uu____5625.FStar_Syntax_Syntax.n  in
                 (match uu____5624 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____5666 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____5685 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____5692 -> false
  
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
      let uu____5740 =
        let uu____5741 = pre_typ t  in uu____5741.FStar_Syntax_Syntax.n  in
      match uu____5740 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____5745 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____5756 =
        let uu____5757 = pre_typ t  in uu____5757.FStar_Syntax_Syntax.n  in
      match uu____5756 with
      | FStar_Syntax_Syntax.Tm_fvar uu____5760 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____5762) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5784) ->
          is_constructed_typ t1 lid
      | uu____5789 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____5800 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____5801 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____5802 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5804) -> get_tycon t2
    | uu____5825 -> FStar_Pervasives_Native.None
  
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
    let uu____5839 =
      let uu____5840 = un_uinst t  in uu____5840.FStar_Syntax_Syntax.n  in
    match uu____5839 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____5844 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____5851 =
        let uu____5854 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____5854  in
      match uu____5851 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____5867 -> false
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
  fun uu____5883  ->
    let u =
      let uu____5889 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_5  -> FStar_Syntax_Syntax.U_unif _0_5)
        uu____5889
       in
    let uu____5906 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____5906, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____5917 = eq_tm a a'  in
      match uu____5917 with | Equal  -> true | uu____5918 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____5921 =
    let uu____5928 =
      let uu____5929 =
        let uu____5930 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____5930
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____5929  in
    FStar_Syntax_Syntax.mk uu____5928  in
  uu____5921 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____6009 =
            let uu____6012 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____6013 =
              let uu____6020 =
                let uu____6021 =
                  let uu____6036 =
                    let uu____6045 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____6052 =
                      let uu____6061 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____6061]  in
                    uu____6045 :: uu____6052  in
                  (tand, uu____6036)  in
                FStar_Syntax_Syntax.Tm_app uu____6021  in
              FStar_Syntax_Syntax.mk uu____6020  in
            uu____6013 FStar_Pervasives_Native.None uu____6012  in
          FStar_Pervasives_Native.Some uu____6009
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____6130 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____6131 =
          let uu____6138 =
            let uu____6139 =
              let uu____6154 =
                let uu____6163 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____6170 =
                  let uu____6179 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____6179]  in
                uu____6163 :: uu____6170  in
              (op_t, uu____6154)  in
            FStar_Syntax_Syntax.Tm_app uu____6139  in
          FStar_Syntax_Syntax.mk uu____6138  in
        uu____6131 FStar_Pervasives_Native.None uu____6130
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____6228 =
      let uu____6235 =
        let uu____6236 =
          let uu____6251 =
            let uu____6260 = FStar_Syntax_Syntax.as_arg phi  in [uu____6260]
             in
          (t_not, uu____6251)  in
        FStar_Syntax_Syntax.Tm_app uu____6236  in
      FStar_Syntax_Syntax.mk uu____6235  in
    uu____6228 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____6445 =
      let uu____6452 =
        let uu____6453 =
          let uu____6468 =
            let uu____6477 = FStar_Syntax_Syntax.as_arg e  in [uu____6477]
             in
          (b2t_v, uu____6468)  in
        FStar_Syntax_Syntax.Tm_app uu____6453  in
      FStar_Syntax_Syntax.mk uu____6452  in
    uu____6445 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____6529 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____6530 =
        let uu____6537 =
          let uu____6538 =
            let uu____6553 =
              let uu____6562 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____6569 =
                let uu____6578 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____6578]  in
              uu____6562 :: uu____6569  in
            (teq, uu____6553)  in
          FStar_Syntax_Syntax.Tm_app uu____6538  in
        FStar_Syntax_Syntax.mk uu____6537  in
      uu____6530 FStar_Pervasives_Native.None uu____6529
  
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
          let uu____6637 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____6638 =
            let uu____6645 =
              let uu____6646 =
                let uu____6661 =
                  let uu____6670 = FStar_Syntax_Syntax.iarg t  in
                  let uu____6677 =
                    let uu____6686 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____6693 =
                      let uu____6702 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____6702]  in
                    uu____6686 :: uu____6693  in
                  uu____6670 :: uu____6677  in
                (eq_inst, uu____6661)  in
              FStar_Syntax_Syntax.Tm_app uu____6646  in
            FStar_Syntax_Syntax.mk uu____6645  in
          uu____6638 FStar_Pervasives_Native.None uu____6637
  
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
        let uu____6769 =
          let uu____6776 =
            let uu____6777 =
              let uu____6792 =
                let uu____6801 = FStar_Syntax_Syntax.iarg t  in
                let uu____6808 =
                  let uu____6817 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____6824 =
                    let uu____6833 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____6833]  in
                  uu____6817 :: uu____6824  in
                uu____6801 :: uu____6808  in
              (t_has_type1, uu____6792)  in
            FStar_Syntax_Syntax.Tm_app uu____6777  in
          FStar_Syntax_Syntax.mk uu____6776  in
        uu____6769 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____6900 =
          let uu____6907 =
            let uu____6908 =
              let uu____6923 =
                let uu____6932 = FStar_Syntax_Syntax.iarg t  in
                let uu____6939 =
                  let uu____6948 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____6948]  in
                uu____6932 :: uu____6939  in
              (t_with_type1, uu____6923)  in
            FStar_Syntax_Syntax.Tm_app uu____6908  in
          FStar_Syntax_Syntax.mk uu____6907  in
        uu____6900 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu____6988 =
    let uu____6995 =
      let uu____6996 =
        let uu____7003 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____7003, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____6996  in
    FStar_Syntax_Syntax.mk uu____6995  in
  uu____6988 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____7016 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____7029 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____7040 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____7016 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____7061  -> c0)
  
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
        let uu____7139 =
          let uu____7146 =
            let uu____7147 =
              let uu____7162 =
                let uu____7171 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____7178 =
                  let uu____7187 =
                    let uu____7194 =
                      let uu____7195 =
                        let uu____7196 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____7196]  in
                      abs uu____7195 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____7194  in
                  [uu____7187]  in
                uu____7171 :: uu____7178  in
              (fa, uu____7162)  in
            FStar_Syntax_Syntax.Tm_app uu____7147  in
          FStar_Syntax_Syntax.mk uu____7146  in
        uu____7139 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____7301 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____7301
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____7312 -> true
    | uu____7313 -> false
  
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
          let uu____7358 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____7358, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____7386 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____7386, FStar_Pervasives_Native.None, t2)  in
        let uu____7399 =
          let uu____7400 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____7400  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____7399
  
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
      let uu____7474 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7477 =
        let uu____7486 = FStar_Syntax_Syntax.as_arg p  in [uu____7486]  in
      mk_app uu____7474 uu____7477
  
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
      let uu____7518 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7521 =
        let uu____7530 = FStar_Syntax_Syntax.as_arg p  in [uu____7530]  in
      mk_app uu____7518 uu____7521
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7558 = head_and_args t  in
    match uu____7558 with
    | (head1,args) ->
        let uu____7599 =
          let uu____7612 =
            let uu____7613 = un_uinst head1  in
            uu____7613.FStar_Syntax_Syntax.n  in
          (uu____7612, args)  in
        (match uu____7599 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____7630)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____7682 =
                    let uu____7687 =
                      let uu____7688 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____7688]  in
                    FStar_Syntax_Subst.open_term uu____7687 p  in
                  (match uu____7682 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____7729 -> failwith "impossible"  in
                       let uu____7734 =
                         let uu____7735 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____7735
                          in
                       if uu____7734
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____7745 -> FStar_Pervasives_Native.None)
         | uu____7748 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7776 = head_and_args t  in
    match uu____7776 with
    | (head1,args) ->
        let uu____7821 =
          let uu____7834 =
            let uu____7835 = FStar_Syntax_Subst.compress head1  in
            uu____7835.FStar_Syntax_Syntax.n  in
          (uu____7834, args)  in
        (match uu____7821 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____7855;
               FStar_Syntax_Syntax.vars = uu____7856;_},u::[]),(t1,uu____7859)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____7896 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7928 = head_and_args t  in
    match uu____7928 with
    | (head1,args) ->
        let uu____7973 =
          let uu____7986 =
            let uu____7987 = FStar_Syntax_Subst.compress head1  in
            uu____7987.FStar_Syntax_Syntax.n  in
          (uu____7986, args)  in
        (match uu____7973 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____8007;
               FStar_Syntax_Syntax.vars = uu____8008;_},u::[]),(t1,uu____8011)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____8048 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8072 = let uu____8087 = unmeta t  in head_and_args uu____8087
       in
    match uu____8072 with
    | (head1,uu____8089) ->
        let uu____8110 =
          let uu____8111 = un_uinst head1  in
          uu____8111.FStar_Syntax_Syntax.n  in
        (match uu____8110 with
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
         | uu____8115 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8133 =
      let uu____8144 =
        let uu____8145 = FStar_Syntax_Subst.compress t  in
        uu____8145.FStar_Syntax_Syntax.n  in
      match uu____8144 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____8248 =
            let uu____8257 =
              let uu____8258 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____8258  in
            (b, uu____8257)  in
          FStar_Pervasives_Native.Some uu____8248
      | uu____8271 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____8133
      (fun uu____8303  ->
         match uu____8303 with
         | (b,c) ->
             let uu____8332 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____8332 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____8379 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____8406 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8406
  
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
    match projectee with | QAll _0 -> true | uu____8454 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____8492 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____8528 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____8565) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____8577) ->
          unmeta_monadic t
      | uu____8590 -> f2  in
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
      let aux f2 uu____8674 =
        match uu____8674 with
        | (lid,arity) ->
            let uu____8683 =
              let uu____8698 = unmeta_monadic f2  in head_and_args uu____8698
               in
            (match uu____8683 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____8724 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____8724
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____8793 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____8793)
      | uu____8804 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____8859 = head_and_args t1  in
        match uu____8859 with
        | (t2,args) ->
            let uu____8906 = un_uinst t2  in
            let uu____8907 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____8938  ->
                      match uu____8938 with
                      | (t3,imp) ->
                          let uu____8949 = unascribe t3  in (uu____8949, imp)))
               in
            (uu____8906, uu____8907)
         in
      let rec aux qopt out t1 =
        let uu____8990 = let uu____9011 = flat t1  in (qopt, uu____9011)  in
        match uu____8990 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____9046;
                 FStar_Syntax_Syntax.vars = uu____9047;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____9050);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____9051;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____9052;_},uu____9053)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____9130;
                 FStar_Syntax_Syntax.vars = uu____9131;_},uu____9132::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____9135);
                  FStar_Syntax_Syntax.pos = uu____9136;
                  FStar_Syntax_Syntax.vars = uu____9137;_},uu____9138)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9226;
               FStar_Syntax_Syntax.vars = uu____9227;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____9230);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____9231;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____9232;_},uu____9233)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9304 =
              let uu____9307 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9307  in
            aux uu____9304 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9313;
               FStar_Syntax_Syntax.vars = uu____9314;_},uu____9315::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____9318);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____9319;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____9320;_},uu____9321)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9404 =
              let uu____9407 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9407  in
            aux uu____9404 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____9413) ->
            let bs = FStar_List.rev out  in
            let uu____9455 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____9455 with
             | (bs1,t2) ->
                 let uu____9464 = patterns t2  in
                 (match uu____9464 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____9506 -> FStar_Pervasives_Native.None  in
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
      let uu____9578 = un_squash t  in
      FStar_Util.bind_opt uu____9578
        (fun t1  ->
           let uu____9594 = head_and_args' t1  in
           match uu____9594 with
           | (hd1,args) ->
               let uu____9627 =
                 let uu____9632 =
                   let uu____9633 = un_uinst hd1  in
                   uu____9633.FStar_Syntax_Syntax.n  in
                 (uu____9632, (FStar_List.length args))  in
               (match uu____9627 with
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
                | uu____9652 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____9681 = un_squash t  in
      FStar_Util.bind_opt uu____9681
        (fun t1  ->
           let uu____9696 = arrow_one t1  in
           match uu____9696 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____9711 =
                 let uu____9712 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____9712  in
               if uu____9711
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____9719 = comp_to_comp_typ_nouniv c  in
                    uu____9719.FStar_Syntax_Syntax.result_typ  in
                  let uu____9720 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____9720
                  then
                    let uu____9723 = patterns q  in
                    match uu____9723 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____9775 =
                       let uu____9776 =
                         let uu____9781 =
                           let uu____9782 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____9789 =
                             let uu____9798 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____9798]  in
                           uu____9782 :: uu____9789  in
                         (FStar_Parser_Const.imp_lid, uu____9781)  in
                       BaseConn uu____9776  in
                     FStar_Pervasives_Native.Some uu____9775))
           | uu____9823 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____9831 = un_squash t  in
      FStar_Util.bind_opt uu____9831
        (fun t1  ->
           let uu____9862 = head_and_args' t1  in
           match uu____9862 with
           | (hd1,args) ->
               let uu____9895 =
                 let uu____9908 =
                   let uu____9909 = un_uinst hd1  in
                   uu____9909.FStar_Syntax_Syntax.n  in
                 (uu____9908, args)  in
               (match uu____9895 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____9924)::(a2,uu____9926)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____9961 =
                      let uu____9962 = FStar_Syntax_Subst.compress a2  in
                      uu____9962.FStar_Syntax_Syntax.n  in
                    (match uu____9961 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____9969) ->
                         let uu____9996 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____9996 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____10035 -> failwith "impossible"  in
                              let uu____10040 = patterns q1  in
                              (match uu____10040 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____10091 -> FStar_Pervasives_Native.None)
                | uu____10092 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____10113 = destruct_sq_forall phi  in
          (match uu____10113 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____10127 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____10133 = destruct_sq_exists phi  in
          (match uu____10133 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____10147 -> f1)
      | uu____10150 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____10154 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____10154
      (fun uu____10159  ->
         let uu____10160 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____10160
           (fun uu____10165  ->
              let uu____10166 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____10166
                (fun uu____10171  ->
                   let uu____10172 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____10172
                     (fun uu____10177  ->
                        let uu____10178 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____10178
                          (fun uu____10182  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____10194 =
      let uu____10195 = FStar_Syntax_Subst.compress t  in
      uu____10195.FStar_Syntax_Syntax.n  in
    match uu____10194 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____10202) ->
        let uu____10229 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____10229 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____10255 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____10255
             then
               let uu____10258 =
                 let uu____10267 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____10267]  in
               mk_app t uu____10258
             else e1)
    | uu____10287 ->
        let uu____10288 =
          let uu____10297 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____10297]  in
        mk_app t uu____10288
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____10332 =
            let uu____10337 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____10337  in
          let uu____10338 =
            let uu____10339 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____10339  in
          let uu____10342 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____10332 a.FStar_Syntax_Syntax.action_univs uu____10338
            FStar_Parser_Const.effect_Tot_lid uu____10342 [] pos
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
    let uu____10365 =
      let uu____10372 =
        let uu____10373 =
          let uu____10388 =
            let uu____10397 = FStar_Syntax_Syntax.as_arg t  in [uu____10397]
             in
          (reify_, uu____10388)  in
        FStar_Syntax_Syntax.Tm_app uu____10373  in
      FStar_Syntax_Syntax.mk uu____10372  in
    uu____10365 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10435 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____10461 = unfold_lazy i  in delta_qualifier uu____10461
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____10463 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____10464 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____10465 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____10488 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____10503 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____10504 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____10511 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____10512 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____10526) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____10531;
           FStar_Syntax_Syntax.index = uu____10532;
           FStar_Syntax_Syntax.sort = t2;_},uu____10534)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____10542) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____10548,uu____10549) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____10591) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____10612,t2,uu____10614) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____10635,t2) -> delta_qualifier t2
  
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
    let uu____10666 = delta_qualifier t  in incr_delta_depth uu____10666
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____10672 =
      let uu____10673 = FStar_Syntax_Subst.compress t  in
      uu____10673.FStar_Syntax_Syntax.n  in
    match uu____10672 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____10676 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____10690 =
      let uu____10705 = unmeta e  in head_and_args uu____10705  in
    match uu____10690 with
    | (head1,args) ->
        let uu____10732 =
          let uu____10745 =
            let uu____10746 = un_uinst head1  in
            uu____10746.FStar_Syntax_Syntax.n  in
          (uu____10745, args)  in
        (match uu____10732 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10762) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____10782::(hd1,uu____10784)::(tl1,uu____10786)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____10833 =
               let uu____10836 =
                 let uu____10839 = list_elements tl1  in
                 FStar_Util.must uu____10839  in
               hd1 :: uu____10836  in
             FStar_Pervasives_Native.Some uu____10833
         | uu____10848 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____10870 .
    ('Auu____10870 -> 'Auu____10870) ->
      'Auu____10870 Prims.list -> 'Auu____10870 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____10895 = f a  in [uu____10895]
      | x::xs -> let uu____10900 = apply_last f xs  in x :: uu____10900
  
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
          let uu____10946 =
            let uu____10953 =
              let uu____10954 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____10954  in
            FStar_Syntax_Syntax.mk uu____10953  in
          uu____10946 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____10971 =
            let uu____10976 =
              let uu____10977 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____10977
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____10976 args  in
          uu____10971 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____10993 =
            let uu____10998 =
              let uu____10999 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____10999
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____10998 args  in
          uu____10993 FStar_Pervasives_Native.None pos  in
        let uu____11002 =
          let uu____11003 =
            let uu____11004 = FStar_Syntax_Syntax.iarg typ  in [uu____11004]
             in
          nil uu____11003 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____11032 =
                 let uu____11033 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____11040 =
                   let uu____11049 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____11056 =
                     let uu____11065 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____11065]  in
                   uu____11049 :: uu____11056  in
                 uu____11033 :: uu____11040  in
               cons1 uu____11032 t.FStar_Syntax_Syntax.pos) l uu____11002
  
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
    fun uu____11123  ->
      match uu____11123 with
      | (gamma,bs,t) ->
          let ctx_u =
            let uu____11166 = FStar_Syntax_Unionfind.from_id id1  in
            {
              FStar_Syntax_Syntax.ctx_uvar_head = uu____11166;
              FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
              FStar_Syntax_Syntax.ctx_uvar_binders = bs;
              FStar_Syntax_Syntax.ctx_uvar_typ = t;
              FStar_Syntax_Syntax.ctx_uvar_reason = "";
              FStar_Syntax_Syntax.ctx_uvar_should_check = true;
              FStar_Syntax_Syntax.ctx_uvar_range = FStar_Range.dummyRange
            }  in
          (failwith
             "uvar_from_id: not fully supported yet .. delayed substitutions";
           FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_uvar
                (ctx_u, ([], FStar_Pervasives_Native.None)))
             FStar_Pervasives_Native.None FStar_Range.dummyRange)
  
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
        | uu____11259 -> false
  
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
          | uu____11366 -> false
  
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
        | uu____11521 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____11555 = FStar_ST.op_Bang debug_term_eq  in
          if uu____11555
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
        let t11 = let uu____11743 = unmeta_safe t1  in canon_app uu____11743
           in
        let t21 = let uu____11749 = unmeta_safe t2  in canon_app uu____11749
           in
        let uu____11752 =
          let uu____11757 =
            let uu____11758 =
              let uu____11761 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____11761  in
            uu____11758.FStar_Syntax_Syntax.n  in
          let uu____11762 =
            let uu____11763 =
              let uu____11766 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____11766  in
            uu____11763.FStar_Syntax_Syntax.n  in
          (uu____11757, uu____11762)  in
        match uu____11752 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____11767,uu____11768) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____11775,FStar_Syntax_Syntax.Tm_uinst uu____11776) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____11783,uu____11784) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____11809,FStar_Syntax_Syntax.Tm_delayed uu____11810) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____11835,uu____11836) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____11863,FStar_Syntax_Syntax.Tm_ascribed uu____11864) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____11897 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____11897
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____11900 = FStar_Const.eq_const c1 c2  in
            check "const" uu____11900
        | (FStar_Syntax_Syntax.Tm_type
           uu____11901,FStar_Syntax_Syntax.Tm_type uu____11902) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____11951 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____11951) &&
              (let uu____11957 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____11957)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____11996 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____11996) &&
              (let uu____12002 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____12002)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____12016 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____12016)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____12063 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____12063) &&
              (let uu____12065 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____12065)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____12150 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____12150) &&
              (let uu____12152 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____12152)
        | (FStar_Syntax_Syntax.Tm_lazy uu____12167,uu____12168) ->
            let uu____12169 =
              let uu____12170 = unlazy t11  in
              term_eq_dbg dbg uu____12170 t21  in
            check "lazy_l" uu____12169
        | (uu____12171,FStar_Syntax_Syntax.Tm_lazy uu____12172) ->
            let uu____12173 =
              let uu____12174 = unlazy t21  in
              term_eq_dbg dbg t11 uu____12174  in
            check "lazy_r" uu____12173
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____12210 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____12210))
              &&
              (let uu____12212 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____12212)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____12214),FStar_Syntax_Syntax.Tm_uvar (u2,uu____12216)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (check "tm_quoted qi" (qi1 = qi2)) &&
              (let uu____12280 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____12280)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____12307 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____12307) &&
                   (let uu____12309 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____12309)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____12326 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____12326) &&
                    (let uu____12328 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____12328))
                   &&
                   (let uu____12330 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____12330)
             | uu____12331 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____12336) -> fail "unk"
        | (uu____12337,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____12338,uu____12339) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____12340,uu____12341) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____12342,uu____12343) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____12344,uu____12345) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____12346,uu____12347) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____12348,uu____12349) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____12366,uu____12367) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____12380,uu____12381) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____12388,uu____12389) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____12404,uu____12405) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____12428,uu____12429) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____12442,uu____12443) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____12458,uu____12459) ->
            fail "bottom"
        | (uu____12466,FStar_Syntax_Syntax.Tm_bvar uu____12467) ->
            fail "bottom"
        | (uu____12468,FStar_Syntax_Syntax.Tm_name uu____12469) ->
            fail "bottom"
        | (uu____12470,FStar_Syntax_Syntax.Tm_fvar uu____12471) ->
            fail "bottom"
        | (uu____12472,FStar_Syntax_Syntax.Tm_constant uu____12473) ->
            fail "bottom"
        | (uu____12474,FStar_Syntax_Syntax.Tm_type uu____12475) ->
            fail "bottom"
        | (uu____12476,FStar_Syntax_Syntax.Tm_abs uu____12477) ->
            fail "bottom"
        | (uu____12494,FStar_Syntax_Syntax.Tm_arrow uu____12495) ->
            fail "bottom"
        | (uu____12508,FStar_Syntax_Syntax.Tm_refine uu____12509) ->
            fail "bottom"
        | (uu____12516,FStar_Syntax_Syntax.Tm_app uu____12517) ->
            fail "bottom"
        | (uu____12532,FStar_Syntax_Syntax.Tm_match uu____12533) ->
            fail "bottom"
        | (uu____12556,FStar_Syntax_Syntax.Tm_let uu____12557) ->
            fail "bottom"
        | (uu____12570,FStar_Syntax_Syntax.Tm_uvar uu____12571) ->
            fail "bottom"
        | (uu____12586,FStar_Syntax_Syntax.Tm_meta uu____12587) ->
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
               let uu____12614 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____12614)
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
               let uu____12635 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____12635)
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
        ((let uu____12655 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____12655) &&
           (let uu____12657 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____12657))
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
    fun uu____12662  ->
      fun uu____12663  ->
        match (uu____12662, uu____12663) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____12788 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____12788) &&
               (let uu____12790 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____12790))
              &&
              (let uu____12792 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____12807 -> false  in
               check "branch when" uu____12792)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____12821 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____12821) &&
           (let uu____12827 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____12827))
          &&
          (let uu____12829 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____12829)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____12841 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____12841 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____12894 ->
        let uu____12919 =
          let uu____12920 = FStar_Syntax_Subst.compress t  in
          sizeof uu____12920  in
        (Prims.parse_int "1") + uu____12919
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____12922 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____12922
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____12924 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____12924
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____12931 = sizeof t1  in (FStar_List.length us) + uu____12931
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____12934) ->
        let uu____12955 = sizeof t1  in
        let uu____12956 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____12967  ->
                 match uu____12967 with
                 | (bv,uu____12973) ->
                     let uu____12974 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____12974) (Prims.parse_int "0") bs
           in
        uu____12955 + uu____12956
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____12997 = sizeof hd1  in
        let uu____12998 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____13009  ->
                 match uu____13009 with
                 | (arg,uu____13015) ->
                     let uu____13016 = sizeof arg  in acc + uu____13016)
            (Prims.parse_int "0") args
           in
        uu____12997 + uu____12998
    | uu____13017 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____13028 =
        let uu____13029 = un_uinst t  in uu____13029.FStar_Syntax_Syntax.n
         in
      match uu____13028 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____13033 -> false
  
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
        let uu____13074 = FStar_Options.set_options t s  in
        match uu____13074 with
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
          ((let uu____13082 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____13082 (fun a237  -> ()));
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
    | FStar_Syntax_Syntax.Tm_delayed uu____13108 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____13136 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____13153 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____13154 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____13155 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____13164) ->
        let uu____13185 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____13185 with
         | (bs1,t2) ->
             let uu____13194 =
               FStar_List.collect
                 (fun uu____13204  ->
                    match uu____13204 with
                    | (b,uu____13212) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____13213 = unbound_variables t2  in
             FStar_List.append uu____13194 uu____13213)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____13234 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____13234 with
         | (bs1,c1) ->
             let uu____13243 =
               FStar_List.collect
                 (fun uu____13253  ->
                    match uu____13253 with
                    | (b,uu____13261) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____13262 = unbound_variables_comp c1  in
             FStar_List.append uu____13243 uu____13262)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____13271 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____13271 with
         | (bs,t2) ->
             let uu____13288 =
               FStar_List.collect
                 (fun uu____13298  ->
                    match uu____13298 with
                    | (b1,uu____13306) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____13307 = unbound_variables t2  in
             FStar_List.append uu____13288 uu____13307)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____13332 =
          FStar_List.collect
            (fun uu____13344  ->
               match uu____13344 with
               | (x,uu____13354) -> unbound_variables x) args
           in
        let uu____13359 = unbound_variables t1  in
        FStar_List.append uu____13332 uu____13359
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____13400 = unbound_variables t1  in
        let uu____13403 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____13418 = FStar_Syntax_Subst.open_branch br  in
                  match uu____13418 with
                  | (p,wopt,t2) ->
                      let uu____13440 = unbound_variables t2  in
                      let uu____13443 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____13440 uu____13443))
           in
        FStar_List.append uu____13400 uu____13403
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____13457) ->
        let uu____13498 = unbound_variables t1  in
        let uu____13501 =
          let uu____13504 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____13535 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____13504 uu____13535  in
        FStar_List.append uu____13498 uu____13501
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____13573 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____13576 =
          let uu____13579 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____13582 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____13587 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____13589 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____13589 with
                 | (uu____13604,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____13579 uu____13582  in
        FStar_List.append uu____13573 uu____13576
    | FStar_Syntax_Syntax.Tm_let ((uu____13606,lbs),t1) ->
        let uu____13623 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____13623 with
         | (lbs1,t2) ->
             let uu____13638 = unbound_variables t2  in
             let uu____13641 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____13648 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____13651 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____13648 uu____13651) lbs1
                in
             FStar_List.append uu____13638 uu____13641)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____13668 = unbound_variables t1  in
        let uu____13671 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____13704  ->
                      match uu____13704 with
                      | (a,uu____13714) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____13719,uu____13720,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____13726,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____13732 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____13739 -> []
          | FStar_Syntax_Syntax.Meta_named uu____13740 -> []  in
        FStar_List.append uu____13668 uu____13671

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____13747) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____13757) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____13767 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____13770 =
          FStar_List.collect
            (fun uu____13782  ->
               match uu____13782 with
               | (a,uu____13792) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____13767 uu____13770
