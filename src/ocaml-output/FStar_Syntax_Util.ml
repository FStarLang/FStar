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
      let uu___79_1279 = c  in
      let uu____1280 =
        let uu____1281 =
          let uu___80_1282 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___80_1282.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___80_1282.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___80_1282.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___80_1282.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1281  in
      {
        FStar_Syntax_Syntax.n = uu____1280;
        FStar_Syntax_Syntax.pos = (uu___79_1279.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___79_1279.FStar_Syntax_Syntax.vars)
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
              let uu___81_1327 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___81_1327.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___81_1327.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___81_1327.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___81_1327.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___82_1328 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___82_1328.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___82_1328.FStar_Syntax_Syntax.vars)
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
            (fun uu___67_1408  ->
               match uu___67_1408 with
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
            (fun uu___68_1418  ->
               match uu___68_1418 with
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
            (fun uu___69_1428  ->
               match uu___69_1428 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1429 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___70_1442  ->
            match uu___70_1442 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1443 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___71_1452  ->
            match uu___71_1452 with
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
                (fun uu___72_1499  ->
                   match uu___72_1499 with
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
let (is_pure_or_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  -> (is_pure_effect l) || (is_ghost_effect l) 
let (is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___73_1533  ->
               match uu___73_1533 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1534 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1545 =
      let uu____1546 = FStar_Syntax_Subst.compress t  in
      uu____1546.FStar_Syntax_Syntax.n  in
    match uu____1545 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1549,c) -> is_pure_or_ghost_comp c
    | uu____1567 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1578 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1584 =
      let uu____1585 = FStar_Syntax_Subst.compress t  in
      uu____1585.FStar_Syntax_Syntax.n  in
    match uu____1584 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1588,c) -> is_lemma_comp c
    | uu____1606 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1612 =
      let uu____1613 = FStar_Syntax_Subst.compress t  in
      uu____1613.FStar_Syntax_Syntax.n  in
    match uu____1612 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1617) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____1639) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____1676,t1,uu____1678) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1700,uu____1701) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1743) -> head_of t1
    | uu____1748 -> t
  
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
    | uu____1815 -> (t1, [])
  
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
        let uu____1884 = head_and_args' head1  in
        (match uu____1884 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1941 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1963) ->
        FStar_Syntax_Subst.compress t2
    | uu____1968 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1974 =
      let uu____1975 = FStar_Syntax_Subst.compress t  in
      uu____1975.FStar_Syntax_Syntax.n  in
    match uu____1974 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1978,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____2000)::uu____2001 ->
                  let pats' = unmeta pats  in
                  let uu____2045 = head_and_args pats'  in
                  (match uu____2045 with
                   | (head1,uu____2061) ->
                       let uu____2082 =
                         let uu____2083 = un_uinst head1  in
                         uu____2083.FStar_Syntax_Syntax.n  in
                       (match uu____2082 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____2087 -> false))
              | uu____2088 -> false)
         | uu____2097 -> false)
    | uu____2098 -> false
  
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
                (fun uu___74_2112  ->
                   match uu___74_2112 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2113 -> false)))
    | uu____2114 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2129) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2139) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2167 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2176 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___83_2188 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___83_2188.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___83_2188.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___83_2188.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___83_2188.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2201  ->
           let uu____2202 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____2202 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___75_2217  ->
            match uu___75_2217 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2218 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2224 -> []
    | FStar_Syntax_Syntax.GTotal uu____2239 -> []
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
    | uu____2274 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2282,uu____2283) ->
        unascribe e2
    | uu____2324 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2376,uu____2377) ->
          ascribe t' k
      | uu____2418 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2444 =
      let uu____2453 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2453  in
    uu____2444 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2512 =
      let uu____2513 = FStar_Syntax_Subst.compress t  in
      uu____2513.FStar_Syntax_Syntax.n  in
    match uu____2512 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2517 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2517
    | uu____2518 -> t
  
let rec unlazy_as_t :
  'Auu____2525 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2525
  =
  fun k  ->
    fun t  ->
      let uu____2536 =
        let uu____2537 = FStar_Syntax_Subst.compress t  in
        uu____2537.FStar_Syntax_Syntax.n  in
      match uu____2536 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.typ = uu____2542;
            FStar_Syntax_Syntax.rng = uu____2543;_}
          when k = k' -> FStar_Dyn.undyn v1
      | uu____2546 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2585 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2585;
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
    let uu____2597 =
      let uu____2610 = unascribe t  in head_and_args' uu____2610  in
    match uu____2597 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2636 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2642 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2648 -> false
  
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
      let equal_if uu___76_2724 = if uu___76_2724 then Equal else Unknown  in
      let equal_iff uu___77_2731 = if uu___77_2731 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2749 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2761) -> NotEqual
        | (uu____2762,NotEqual ) -> NotEqual
        | (Unknown ,uu____2763) -> Unknown
        | (uu____2764,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____2810 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2810
        then
          let uu____2812 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2870  ->
                    match uu____2870 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2896 = eq_tm a1 a2  in
                        eq_inj acc uu____2896) Equal) uu____2812
        else NotEqual  in
      let uu____2898 =
        let uu____2903 =
          let uu____2904 = unmeta t11  in uu____2904.FStar_Syntax_Syntax.n
           in
        let uu____2907 =
          let uu____2908 = unmeta t21  in uu____2908.FStar_Syntax_Syntax.n
           in
        (uu____2903, uu____2907)  in
      match uu____2898 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2913,uu____2914) ->
          let uu____2915 = unlazy t11  in eq_tm uu____2915 t21
      | (uu____2916,FStar_Syntax_Syntax.Tm_lazy uu____2917) ->
          let uu____2918 = unlazy t21  in eq_tm t11 uu____2918
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
            (let uu____2936 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2936)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2949 = eq_tm f g  in
          eq_and uu____2949
            (fun uu____2952  ->
               let uu____2953 = eq_univs_list us vs  in equal_if uu____2953)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2954),uu____2955) -> Unknown
      | (uu____2956,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2957)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2960 = FStar_Const.eq_const c d  in equal_iff uu____2960
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____2962)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____2964))) ->
          let uu____3005 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3005
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3050 =
            let uu____3055 =
              let uu____3056 = un_uinst h1  in
              uu____3056.FStar_Syntax_Syntax.n  in
            let uu____3059 =
              let uu____3060 = un_uinst h2  in
              uu____3060.FStar_Syntax_Syntax.n  in
            (uu____3055, uu____3059)  in
          (match uu____3050 with
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
                 (let uu____3072 =
                    let uu____3073 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3073  in
                  FStar_List.mem uu____3072 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3074 ->
               let uu____3079 = eq_tm h1 h2  in
               eq_and uu____3079 (fun uu____3081  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3186 = FStar_List.zip bs1 bs2  in
            let uu____3249 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3286  ->
                 fun a  ->
                   match uu____3286 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3379  -> branch_matches b1 b2))
              uu____3186 uu____3249
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3383 = eq_univs u v1  in equal_if uu____3383
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) -> if q1 = q2 then eq_tm t12 t22 else Unknown
      | uu____3397 -> Unknown

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
        | (uu____3480,uu____3481) -> false  in
      let uu____3490 = b1  in
      match uu____3490 with
      | (p1,w1,t1) ->
          let uu____3524 = b2  in
          (match uu____3524 with
           | (p2,w2,t2) ->
               let uu____3558 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3558
               then
                 let uu____3559 =
                   (let uu____3562 = eq_tm t1 t2  in uu____3562 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3571 = eq_tm t11 t21  in
                             uu____3571 = Equal) w1 w2)
                    in
                 (if uu____3559 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3621)::a11,(b,uu____3624)::b1) ->
          let uu____3678 = eq_tm a b  in
          (match uu____3678 with
           | Equal  -> eq_args a11 b1
           | uu____3679 -> Unknown)
      | uu____3680 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3710) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3716,uu____3717) ->
        unrefine t2
    | uu____3758 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3764 =
      let uu____3765 = FStar_Syntax_Subst.compress t  in
      uu____3765.FStar_Syntax_Syntax.n  in
    match uu____3764 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3768 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3784) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____3789 ->
        let uu____3804 =
          let uu____3805 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____3805 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____3804 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3859,uu____3860) ->
        is_uvar t1
    | uu____3901 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3907 =
      let uu____3908 = unrefine t  in uu____3908.FStar_Syntax_Syntax.n  in
    match uu____3907 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3913) -> is_unit t1
    | uu____3918 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3924 =
      let uu____3925 = unrefine t  in uu____3925.FStar_Syntax_Syntax.n  in
    match uu____3924 with
    | FStar_Syntax_Syntax.Tm_type uu____3928 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3931) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3953) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3958,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3976 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____3982 =
      let uu____3983 = FStar_Syntax_Subst.compress e  in
      uu____3983.FStar_Syntax_Syntax.n  in
    match uu____3982 with
    | FStar_Syntax_Syntax.Tm_abs uu____3986 -> true
    | uu____4003 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4009 =
      let uu____4010 = FStar_Syntax_Subst.compress t  in
      uu____4010.FStar_Syntax_Syntax.n  in
    match uu____4009 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4013 -> true
    | uu____4026 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4034) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4040,uu____4041) ->
        pre_typ t2
    | uu____4082 -> t1
  
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
      let uu____4104 =
        let uu____4105 = un_uinst typ1  in uu____4105.FStar_Syntax_Syntax.n
         in
      match uu____4104 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____4160 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____4184 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____4202,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____4209) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____4214,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____4225,uu____4226,uu____4227,uu____4228,uu____4229) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____4239,uu____4240,uu____4241,uu____4242) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____4248,uu____4249,uu____4250,uu____4251,uu____4252) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____4258,uu____4259) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4261,uu____4262) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____4265 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____4266 -> []
    | FStar_Syntax_Syntax.Sig_main uu____4267 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____4280 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___78_4303  ->
    match uu___78_4303 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____4316 'Auu____4317 .
    ('Auu____4316 FStar_Syntax_Syntax.syntax,'Auu____4317)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____4328  ->
    match uu____4328 with | (hd1,uu____4336) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____4349 'Auu____4350 .
    ('Auu____4349 FStar_Syntax_Syntax.syntax,'Auu____4350)
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
      | uu____4441 ->
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
          let uu____4501 = FStar_Ident.range_of_lid l  in
          let uu____4502 =
            let uu____4511 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____4511  in
          uu____4502 FStar_Pervasives_Native.None uu____4501
      | uu____4519 ->
          let e =
            let uu____4531 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____4531 args  in
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
      let uu____4546 =
        let uu____4551 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____4551, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____4546
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
          let uu____4602 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____4602
          then
            let uu____4603 =
              let uu____4608 =
                let uu____4609 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____4609  in
              let uu____4610 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____4608, uu____4610)  in
            FStar_Ident.mk_ident uu____4603
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___84_4613 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___84_4613.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___84_4613.FStar_Syntax_Syntax.sort)
          }  in
        let uu____4614 = mk_field_projector_name_from_ident lid nm  in
        (uu____4614, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4625) -> ses
    | uu____4634 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____4643 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____4654 = FStar_Syntax_Unionfind.find uv  in
      match uu____4654 with
      | FStar_Pervasives_Native.Some uu____4657 ->
          let uu____4658 =
            let uu____4659 =
              let uu____4660 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____4660  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4659  in
          failwith uu____4658
      | uu____4661 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____4736 -> q1 = q2
  
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
              let uu____4781 =
                let uu___85_4782 = rc  in
                let uu____4783 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___85_4782.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____4783;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___85_4782.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____4781
           in
        match bs with
        | [] -> t
        | uu____4798 ->
            let body =
              let uu____4800 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4800  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4830 =
                   let uu____4837 =
                     let uu____4838 =
                       let uu____4855 =
                         let uu____4862 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4862 bs'  in
                       let uu____4873 = close_lopt lopt'  in
                       (uu____4855, t1, uu____4873)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4838  in
                   FStar_Syntax_Syntax.mk uu____4837  in
                 uu____4830 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4889 ->
                 let uu____4896 =
                   let uu____4903 =
                     let uu____4904 =
                       let uu____4921 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4928 = close_lopt lopt  in
                       (uu____4921, body, uu____4928)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4904  in
                   FStar_Syntax_Syntax.mk uu____4903  in
                 uu____4896 FStar_Pervasives_Native.None
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
      | uu____4978 ->
          let uu____4985 =
            let uu____4992 =
              let uu____4993 =
                let uu____5006 = FStar_Syntax_Subst.close_binders bs  in
                let uu____5013 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____5006, uu____5013)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4993  in
            FStar_Syntax_Syntax.mk uu____4992  in
          uu____4985 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____5058 =
        let uu____5059 = FStar_Syntax_Subst.compress t  in
        uu____5059.FStar_Syntax_Syntax.n  in
      match uu____5058 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____5085) ->
               let uu____5094 =
                 let uu____5095 = FStar_Syntax_Subst.compress tres  in
                 uu____5095.FStar_Syntax_Syntax.n  in
               (match uu____5094 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____5130 -> t)
           | uu____5131 -> t)
      | uu____5132 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____5149 =
        let uu____5150 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____5150 t.FStar_Syntax_Syntax.pos  in
      let uu____5151 =
        let uu____5158 =
          let uu____5159 =
            let uu____5166 =
              let uu____5169 =
                let uu____5170 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____5170]  in
              FStar_Syntax_Subst.close uu____5169 t  in
            (b, uu____5166)  in
          FStar_Syntax_Syntax.Tm_refine uu____5159  in
        FStar_Syntax_Syntax.mk uu____5158  in
      uu____5151 FStar_Pervasives_Native.None uu____5149
  
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
        let uu____5237 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____5237 with
         | (bs1,c1) ->
             let uu____5254 = is_total_comp c1  in
             if uu____5254
             then
               let uu____5265 = arrow_formals_comp (comp_result c1)  in
               (match uu____5265 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____5317;
           FStar_Syntax_Syntax.index = uu____5318;
           FStar_Syntax_Syntax.sort = k2;_},uu____5320)
        -> arrow_formals_comp k2
    | uu____5327 ->
        let uu____5328 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____5328)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____5356 = arrow_formals_comp k  in
    match uu____5356 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____5438 =
            let uu___86_5439 = rc  in
            let uu____5440 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___86_5439.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____5440;
              FStar_Syntax_Syntax.residual_flags =
                (uu___86_5439.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____5438
      | uu____5449 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____5481 =
        let uu____5482 =
          let uu____5485 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____5485  in
        uu____5482.FStar_Syntax_Syntax.n  in
      match uu____5481 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____5525 = aux t2 what  in
          (match uu____5525 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____5585 -> ([], t1, abs_body_lcomp)  in
    let uu____5598 = aux t FStar_Pervasives_Native.None  in
    match uu____5598 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____5640 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____5640 with
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
                    | (FStar_Pervasives_Native.None ,uu____5801) -> def
                    | (uu____5812,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____5824) ->
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
            let uu____5910 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____5910 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5939 ->
            let t' = arrow binders c  in
            let uu____5949 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5949 with
             | (uvs1,t'1) ->
                 let uu____5968 =
                   let uu____5969 = FStar_Syntax_Subst.compress t'1  in
                   uu____5969.FStar_Syntax_Syntax.n  in
                 (match uu____5968 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____6010 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____6029 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____6036 -> false
  
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
      let uu____6084 =
        let uu____6085 = pre_typ t  in uu____6085.FStar_Syntax_Syntax.n  in
      match uu____6084 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____6089 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____6100 =
        let uu____6101 = pre_typ t  in uu____6101.FStar_Syntax_Syntax.n  in
      match uu____6100 with
      | FStar_Syntax_Syntax.Tm_fvar uu____6104 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____6106) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6128) ->
          is_constructed_typ t1 lid
      | uu____6133 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____6144 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____6145 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____6146 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____6148) -> get_tycon t2
    | uu____6169 -> FStar_Pervasives_Native.None
  
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
    let uu____6183 =
      let uu____6184 = un_uinst t  in uu____6184.FStar_Syntax_Syntax.n  in
    match uu____6183 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____6188 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____6195 =
        let uu____6198 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____6198  in
      match uu____6195 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____6211 -> false
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
  fun uu____6223  ->
    let u =
      let uu____6229 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_5  -> FStar_Syntax_Syntax.U_unif _0_5)
        uu____6229
       in
    let uu____6246 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____6246, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____6257 = eq_tm a a'  in
      match uu____6257 with | Equal  -> true | uu____6258 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____6261 =
    let uu____6268 =
      let uu____6269 =
        let uu____6270 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____6270
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____6269  in
    FStar_Syntax_Syntax.mk uu____6268  in
  uu____6261 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____6343 =
            let uu____6346 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____6347 =
              let uu____6354 =
                let uu____6355 =
                  let uu____6370 =
                    let uu____6379 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____6386 =
                      let uu____6395 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____6395]  in
                    uu____6379 :: uu____6386  in
                  (tand, uu____6370)  in
                FStar_Syntax_Syntax.Tm_app uu____6355  in
              FStar_Syntax_Syntax.mk uu____6354  in
            uu____6347 FStar_Pervasives_Native.None uu____6346  in
          FStar_Pervasives_Native.Some uu____6343
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____6464 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____6465 =
          let uu____6472 =
            let uu____6473 =
              let uu____6488 =
                let uu____6497 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____6504 =
                  let uu____6513 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____6513]  in
                uu____6497 :: uu____6504  in
              (op_t, uu____6488)  in
            FStar_Syntax_Syntax.Tm_app uu____6473  in
          FStar_Syntax_Syntax.mk uu____6472  in
        uu____6465 FStar_Pervasives_Native.None uu____6464
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____6562 =
      let uu____6569 =
        let uu____6570 =
          let uu____6585 =
            let uu____6594 = FStar_Syntax_Syntax.as_arg phi  in [uu____6594]
             in
          (t_not, uu____6585)  in
        FStar_Syntax_Syntax.Tm_app uu____6570  in
      FStar_Syntax_Syntax.mk uu____6569  in
    uu____6562 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____6779 =
      let uu____6786 =
        let uu____6787 =
          let uu____6802 =
            let uu____6811 = FStar_Syntax_Syntax.as_arg e  in [uu____6811]
             in
          (b2t_v, uu____6802)  in
        FStar_Syntax_Syntax.Tm_app uu____6787  in
      FStar_Syntax_Syntax.mk uu____6786  in
    uu____6779 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____6848 =
      let uu____6849 = unmeta t  in uu____6849.FStar_Syntax_Syntax.n  in
    match uu____6848 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____6853 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____6874 = is_t_true t1  in
      if uu____6874
      then t2
      else
        (let uu____6878 = is_t_true t2  in
         if uu____6878 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____6902 = is_t_true t1  in
      if uu____6902
      then t_true
      else
        (let uu____6906 = is_t_true t2  in
         if uu____6906 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____6930 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____6931 =
        let uu____6938 =
          let uu____6939 =
            let uu____6954 =
              let uu____6963 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____6970 =
                let uu____6979 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____6979]  in
              uu____6963 :: uu____6970  in
            (teq, uu____6954)  in
          FStar_Syntax_Syntax.Tm_app uu____6939  in
        FStar_Syntax_Syntax.mk uu____6938  in
      uu____6931 FStar_Pervasives_Native.None uu____6930
  
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
          let uu____7038 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____7039 =
            let uu____7046 =
              let uu____7047 =
                let uu____7062 =
                  let uu____7071 = FStar_Syntax_Syntax.iarg t  in
                  let uu____7078 =
                    let uu____7087 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____7094 =
                      let uu____7103 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____7103]  in
                    uu____7087 :: uu____7094  in
                  uu____7071 :: uu____7078  in
                (eq_inst, uu____7062)  in
              FStar_Syntax_Syntax.Tm_app uu____7047  in
            FStar_Syntax_Syntax.mk uu____7046  in
          uu____7039 FStar_Pervasives_Native.None uu____7038
  
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
        let uu____7170 =
          let uu____7177 =
            let uu____7178 =
              let uu____7193 =
                let uu____7202 = FStar_Syntax_Syntax.iarg t  in
                let uu____7209 =
                  let uu____7218 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____7225 =
                    let uu____7234 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____7234]  in
                  uu____7218 :: uu____7225  in
                uu____7202 :: uu____7209  in
              (t_has_type1, uu____7193)  in
            FStar_Syntax_Syntax.Tm_app uu____7178  in
          FStar_Syntax_Syntax.mk uu____7177  in
        uu____7170 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____7301 =
          let uu____7308 =
            let uu____7309 =
              let uu____7324 =
                let uu____7333 = FStar_Syntax_Syntax.iarg t  in
                let uu____7340 =
                  let uu____7349 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____7349]  in
                uu____7333 :: uu____7340  in
              (t_with_type1, uu____7324)  in
            FStar_Syntax_Syntax.Tm_app uu____7309  in
          FStar_Syntax_Syntax.mk uu____7308  in
        uu____7301 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____7387 =
    let uu____7394 =
      let uu____7395 =
        let uu____7402 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____7402, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____7395  in
    FStar_Syntax_Syntax.mk uu____7394  in
  uu____7387 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____7415 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____7428 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____7439 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____7415 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____7460  -> c0)
  
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
        let uu____7538 =
          let uu____7545 =
            let uu____7546 =
              let uu____7561 =
                let uu____7570 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____7577 =
                  let uu____7586 =
                    let uu____7593 =
                      let uu____7594 =
                        let uu____7595 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____7595]  in
                      abs uu____7594 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____7593  in
                  [uu____7586]  in
                uu____7570 :: uu____7577  in
              (fa, uu____7561)  in
            FStar_Syntax_Syntax.Tm_app uu____7546  in
          FStar_Syntax_Syntax.mk uu____7545  in
        uu____7538 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____7700 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____7700
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____7711 -> true
    | uu____7712 -> false
  
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
          let uu____7757 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____7757, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____7785 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____7785, FStar_Pervasives_Native.None, t2)  in
        let uu____7798 =
          let uu____7799 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____7799  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____7798
  
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
      let uu____7873 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7876 =
        let uu____7885 = FStar_Syntax_Syntax.as_arg p  in [uu____7885]  in
      mk_app uu____7873 uu____7876
  
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
      let uu____7917 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7920 =
        let uu____7929 = FStar_Syntax_Syntax.as_arg p  in [uu____7929]  in
      mk_app uu____7917 uu____7920
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7957 = head_and_args t  in
    match uu____7957 with
    | (head1,args) ->
        let uu____7998 =
          let uu____8011 =
            let uu____8012 = un_uinst head1  in
            uu____8012.FStar_Syntax_Syntax.n  in
          (uu____8011, args)  in
        (match uu____7998 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____8029)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____8081 =
                    let uu____8086 =
                      let uu____8087 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____8087]  in
                    FStar_Syntax_Subst.open_term uu____8086 p  in
                  (match uu____8081 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____8128 -> failwith "impossible"  in
                       let uu____8133 =
                         let uu____8134 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____8134
                          in
                       if uu____8133
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____8146 -> FStar_Pervasives_Native.None)
         | uu____8149 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8177 = head_and_args t  in
    match uu____8177 with
    | (head1,args) ->
        let uu____8222 =
          let uu____8235 =
            let uu____8236 = FStar_Syntax_Subst.compress head1  in
            uu____8236.FStar_Syntax_Syntax.n  in
          (uu____8235, args)  in
        (match uu____8222 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____8256;
               FStar_Syntax_Syntax.vars = uu____8257;_},u::[]),(t1,uu____8260)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____8297 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8329 = head_and_args t  in
    match uu____8329 with
    | (head1,args) ->
        let uu____8374 =
          let uu____8387 =
            let uu____8388 = FStar_Syntax_Subst.compress head1  in
            uu____8388.FStar_Syntax_Syntax.n  in
          (uu____8387, args)  in
        (match uu____8374 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____8408;
               FStar_Syntax_Syntax.vars = uu____8409;_},u::[]),(t1,uu____8412)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____8449 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8473 = let uu____8488 = unmeta t  in head_and_args uu____8488
       in
    match uu____8473 with
    | (head1,uu____8490) ->
        let uu____8511 =
          let uu____8512 = un_uinst head1  in
          uu____8512.FStar_Syntax_Syntax.n  in
        (match uu____8511 with
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
         | uu____8516 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8534 =
      let uu____8545 =
        let uu____8546 = FStar_Syntax_Subst.compress t  in
        uu____8546.FStar_Syntax_Syntax.n  in
      match uu____8545 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____8647 =
            let uu____8656 =
              let uu____8657 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____8657  in
            (b, uu____8656)  in
          FStar_Pervasives_Native.Some uu____8647
      | uu____8670 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____8534
      (fun uu____8702  ->
         match uu____8702 with
         | (b,c) ->
             let uu____8731 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____8731 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____8778 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____8805 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8805
  
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
    match projectee with | QAll _0 -> true | uu____8853 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____8891 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____8927 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____8964) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____8976) ->
          unmeta_monadic t
      | uu____8989 -> f2  in
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
      let aux f2 uu____9073 =
        match uu____9073 with
        | (lid,arity) ->
            let uu____9082 =
              let uu____9097 = unmeta_monadic f2  in head_and_args uu____9097
               in
            (match uu____9082 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____9123 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____9123
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____9192 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____9192)
      | uu____9203 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____9258 = head_and_args t1  in
        match uu____9258 with
        | (t2,args) ->
            let uu____9305 = un_uinst t2  in
            let uu____9306 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9337  ->
                      match uu____9337 with
                      | (t3,imp) ->
                          let uu____9348 = unascribe t3  in (uu____9348, imp)))
               in
            (uu____9305, uu____9306)
         in
      let rec aux qopt out t1 =
        let uu____9389 = let uu____9410 = flat t1  in (qopt, uu____9410)  in
        match uu____9389 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____9445;
                 FStar_Syntax_Syntax.vars = uu____9446;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____9449);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____9450;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____9451;_},uu____9452)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____9529;
                 FStar_Syntax_Syntax.vars = uu____9530;_},uu____9531::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____9534);
                  FStar_Syntax_Syntax.pos = uu____9535;
                  FStar_Syntax_Syntax.vars = uu____9536;_},uu____9537)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9625;
               FStar_Syntax_Syntax.vars = uu____9626;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____9629);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____9630;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____9631;_},uu____9632)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9703 =
              let uu____9706 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9706  in
            aux uu____9703 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9712;
               FStar_Syntax_Syntax.vars = uu____9713;_},uu____9714::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____9717);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____9718;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____9719;_},uu____9720)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9803 =
              let uu____9806 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9806  in
            aux uu____9803 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____9812) ->
            let bs = FStar_List.rev out  in
            let uu____9854 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____9854 with
             | (bs1,t2) ->
                 let uu____9863 = patterns t2  in
                 (match uu____9863 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____9905 -> FStar_Pervasives_Native.None  in
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
      let uu____9977 = un_squash t  in
      FStar_Util.bind_opt uu____9977
        (fun t1  ->
           let uu____9993 = head_and_args' t1  in
           match uu____9993 with
           | (hd1,args) ->
               let uu____10026 =
                 let uu____10031 =
                   let uu____10032 = un_uinst hd1  in
                   uu____10032.FStar_Syntax_Syntax.n  in
                 (uu____10031, (FStar_List.length args))  in
               (match uu____10026 with
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
                | uu____10051 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____10080 = un_squash t  in
      FStar_Util.bind_opt uu____10080
        (fun t1  ->
           let uu____10095 = arrow_one t1  in
           match uu____10095 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____10110 =
                 let uu____10111 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____10111  in
               if uu____10110
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____10118 = comp_to_comp_typ_nouniv c  in
                    uu____10118.FStar_Syntax_Syntax.result_typ  in
                  let uu____10119 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____10119
                  then
                    let uu____10122 = patterns q  in
                    match uu____10122 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____10174 =
                       let uu____10175 =
                         let uu____10180 =
                           let uu____10181 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____10188 =
                             let uu____10197 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____10197]  in
                           uu____10181 :: uu____10188  in
                         (FStar_Parser_Const.imp_lid, uu____10180)  in
                       BaseConn uu____10175  in
                     FStar_Pervasives_Native.Some uu____10174))
           | uu____10222 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____10230 = un_squash t  in
      FStar_Util.bind_opt uu____10230
        (fun t1  ->
           let uu____10261 = head_and_args' t1  in
           match uu____10261 with
           | (hd1,args) ->
               let uu____10294 =
                 let uu____10307 =
                   let uu____10308 = un_uinst hd1  in
                   uu____10308.FStar_Syntax_Syntax.n  in
                 (uu____10307, args)  in
               (match uu____10294 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____10323)::(a2,uu____10325)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____10360 =
                      let uu____10361 = FStar_Syntax_Subst.compress a2  in
                      uu____10361.FStar_Syntax_Syntax.n  in
                    (match uu____10360 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____10368) ->
                         let uu____10395 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____10395 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____10434 -> failwith "impossible"  in
                              let uu____10439 = patterns q1  in
                              (match uu____10439 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____10490 -> FStar_Pervasives_Native.None)
                | uu____10491 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____10512 = destruct_sq_forall phi  in
          (match uu____10512 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____10526 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____10532 = destruct_sq_exists phi  in
          (match uu____10532 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____10546 -> f1)
      | uu____10549 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____10553 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____10553
      (fun uu____10558  ->
         let uu____10559 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____10559
           (fun uu____10564  ->
              let uu____10565 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____10565
                (fun uu____10570  ->
                   let uu____10571 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____10571
                     (fun uu____10576  ->
                        let uu____10577 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____10577
                          (fun uu____10581  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____10593 =
      let uu____10594 = FStar_Syntax_Subst.compress t  in
      uu____10594.FStar_Syntax_Syntax.n  in
    match uu____10593 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____10601) ->
        let uu____10628 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____10628 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____10654 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____10654
             then
               let uu____10657 =
                 let uu____10666 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____10666]  in
               mk_app t uu____10657
             else e1)
    | uu____10686 ->
        let uu____10687 =
          let uu____10696 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____10696]  in
        mk_app t uu____10687
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____10731 =
            let uu____10736 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____10736  in
          let uu____10737 =
            let uu____10738 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____10738  in
          let uu____10741 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____10731 a.FStar_Syntax_Syntax.action_univs uu____10737
            FStar_Parser_Const.effect_Tot_lid uu____10741 [] pos
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
    let uu____10764 =
      let uu____10771 =
        let uu____10772 =
          let uu____10787 =
            let uu____10796 = FStar_Syntax_Syntax.as_arg t  in [uu____10796]
             in
          (reify_, uu____10787)  in
        FStar_Syntax_Syntax.Tm_app uu____10772  in
      FStar_Syntax_Syntax.mk uu____10771  in
    uu____10764 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10834 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____10860 = unfold_lazy i  in delta_qualifier uu____10860
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____10862 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____10863 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____10864 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____10887 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____10902 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____10903 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____10910 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____10911 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____10925) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____10930;
           FStar_Syntax_Syntax.index = uu____10931;
           FStar_Syntax_Syntax.sort = t2;_},uu____10933)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____10941) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____10947,uu____10948) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____10990) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____11011,t2,uu____11013) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____11034,t2) -> delta_qualifier t2
  
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
    let uu____11065 = delta_qualifier t  in incr_delta_depth uu____11065
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11071 =
      let uu____11072 = FStar_Syntax_Subst.compress t  in
      uu____11072.FStar_Syntax_Syntax.n  in
    match uu____11071 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____11075 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____11089 =
      let uu____11104 = unmeta e  in head_and_args uu____11104  in
    match uu____11089 with
    | (head1,args) ->
        let uu____11131 =
          let uu____11144 =
            let uu____11145 = un_uinst head1  in
            uu____11145.FStar_Syntax_Syntax.n  in
          (uu____11144, args)  in
        (match uu____11131 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11161) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____11181::(hd1,uu____11183)::(tl1,uu____11185)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____11232 =
               let uu____11235 =
                 let uu____11238 = list_elements tl1  in
                 FStar_Util.must uu____11238  in
               hd1 :: uu____11235  in
             FStar_Pervasives_Native.Some uu____11232
         | uu____11247 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____11269 .
    ('Auu____11269 -> 'Auu____11269) ->
      'Auu____11269 Prims.list -> 'Auu____11269 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____11294 = f a  in [uu____11294]
      | x::xs -> let uu____11299 = apply_last f xs  in x :: uu____11299
  
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
          let uu____11345 =
            let uu____11352 =
              let uu____11353 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____11353  in
            FStar_Syntax_Syntax.mk uu____11352  in
          uu____11345 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____11370 =
            let uu____11375 =
              let uu____11376 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____11376
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____11375 args  in
          uu____11370 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____11392 =
            let uu____11397 =
              let uu____11398 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____11398
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____11397 args  in
          uu____11392 FStar_Pervasives_Native.None pos  in
        let uu____11401 =
          let uu____11402 =
            let uu____11403 = FStar_Syntax_Syntax.iarg typ  in [uu____11403]
             in
          nil uu____11402 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____11431 =
                 let uu____11432 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____11439 =
                   let uu____11448 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____11455 =
                     let uu____11464 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____11464]  in
                   uu____11448 :: uu____11455  in
                 uu____11432 :: uu____11439  in
               cons1 uu____11431 t.FStar_Syntax_Syntax.pos) l uu____11401
  
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
        | uu____11558 -> false
  
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
          | uu____11665 -> false
  
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
        | uu____11820 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____11854 = FStar_ST.op_Bang debug_term_eq  in
          if uu____11854
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
        let t11 = let uu____12042 = unmeta_safe t1  in canon_app uu____12042
           in
        let t21 = let uu____12048 = unmeta_safe t2  in canon_app uu____12048
           in
        let uu____12051 =
          let uu____12056 =
            let uu____12057 =
              let uu____12060 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____12060  in
            uu____12057.FStar_Syntax_Syntax.n  in
          let uu____12061 =
            let uu____12062 =
              let uu____12065 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____12065  in
            uu____12062.FStar_Syntax_Syntax.n  in
          (uu____12056, uu____12061)  in
        match uu____12051 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____12066,uu____12067) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12074,FStar_Syntax_Syntax.Tm_uinst uu____12075) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____12082,uu____12083) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12108,FStar_Syntax_Syntax.Tm_delayed uu____12109) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____12134,uu____12135) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12162,FStar_Syntax_Syntax.Tm_ascribed uu____12163) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____12196 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____12196
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____12199 = FStar_Const.eq_const c1 c2  in
            check "const" uu____12199
        | (FStar_Syntax_Syntax.Tm_type
           uu____12200,FStar_Syntax_Syntax.Tm_type uu____12201) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____12250 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____12250) &&
              (let uu____12256 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____12256)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____12295 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____12295) &&
              (let uu____12301 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____12301)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____12315 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____12315)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____12362 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____12362) &&
              (let uu____12364 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____12364)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____12449 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____12449) &&
              (let uu____12451 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____12451)
        | (FStar_Syntax_Syntax.Tm_lazy uu____12466,uu____12467) ->
            let uu____12468 =
              let uu____12469 = unlazy t11  in
              term_eq_dbg dbg uu____12469 t21  in
            check "lazy_l" uu____12468
        | (uu____12470,FStar_Syntax_Syntax.Tm_lazy uu____12471) ->
            let uu____12472 =
              let uu____12473 = unlazy t21  in
              term_eq_dbg dbg t11 uu____12473  in
            check "lazy_r" uu____12472
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____12509 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____12509))
              &&
              (let uu____12511 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____12511)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____12513),FStar_Syntax_Syntax.Tm_uvar (u2,uu____12515)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (check "tm_quoted qi" (qi1 = qi2)) &&
              (let uu____12579 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____12579)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____12606 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____12606) &&
                   (let uu____12608 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____12608)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____12625 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____12625) &&
                    (let uu____12627 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____12627))
                   &&
                   (let uu____12629 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____12629)
             | uu____12630 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____12635) -> fail "unk"
        | (uu____12636,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____12637,uu____12638) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____12639,uu____12640) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____12641,uu____12642) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____12643,uu____12644) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____12645,uu____12646) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____12647,uu____12648) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____12665,uu____12666) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____12679,uu____12680) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____12687,uu____12688) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____12703,uu____12704) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____12727,uu____12728) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____12741,uu____12742) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____12757,uu____12758) ->
            fail "bottom"
        | (uu____12765,FStar_Syntax_Syntax.Tm_bvar uu____12766) ->
            fail "bottom"
        | (uu____12767,FStar_Syntax_Syntax.Tm_name uu____12768) ->
            fail "bottom"
        | (uu____12769,FStar_Syntax_Syntax.Tm_fvar uu____12770) ->
            fail "bottom"
        | (uu____12771,FStar_Syntax_Syntax.Tm_constant uu____12772) ->
            fail "bottom"
        | (uu____12773,FStar_Syntax_Syntax.Tm_type uu____12774) ->
            fail "bottom"
        | (uu____12775,FStar_Syntax_Syntax.Tm_abs uu____12776) ->
            fail "bottom"
        | (uu____12793,FStar_Syntax_Syntax.Tm_arrow uu____12794) ->
            fail "bottom"
        | (uu____12807,FStar_Syntax_Syntax.Tm_refine uu____12808) ->
            fail "bottom"
        | (uu____12815,FStar_Syntax_Syntax.Tm_app uu____12816) ->
            fail "bottom"
        | (uu____12831,FStar_Syntax_Syntax.Tm_match uu____12832) ->
            fail "bottom"
        | (uu____12855,FStar_Syntax_Syntax.Tm_let uu____12856) ->
            fail "bottom"
        | (uu____12869,FStar_Syntax_Syntax.Tm_uvar uu____12870) ->
            fail "bottom"
        | (uu____12885,FStar_Syntax_Syntax.Tm_meta uu____12886) ->
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
               let uu____12913 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____12913)
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
               let uu____12934 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____12934)
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
        ((let uu____12954 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____12954) &&
           (let uu____12956 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____12956))
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
    fun uu____12961  ->
      fun uu____12962  ->
        match (uu____12961, uu____12962) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____13087 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____13087) &&
               (let uu____13089 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____13089))
              &&
              (let uu____13091 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____13130 -> false  in
               check "branch when" uu____13091)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____13148 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____13148) &&
           (let uu____13154 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____13154))
          &&
          (let uu____13156 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____13156)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____13168 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____13168 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13221 ->
        let uu____13246 =
          let uu____13247 = FStar_Syntax_Subst.compress t  in
          sizeof uu____13247  in
        (Prims.parse_int "1") + uu____13246
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____13249 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____13249
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____13251 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____13251
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____13258 = sizeof t1  in (FStar_List.length us) + uu____13258
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____13261) ->
        let uu____13282 = sizeof t1  in
        let uu____13283 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____13294  ->
                 match uu____13294 with
                 | (bv,uu____13300) ->
                     let uu____13301 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____13301) (Prims.parse_int "0") bs
           in
        uu____13282 + uu____13283
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____13324 = sizeof hd1  in
        let uu____13325 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____13336  ->
                 match uu____13336 with
                 | (arg,uu____13342) ->
                     let uu____13343 = sizeof arg  in acc + uu____13343)
            (Prims.parse_int "0") args
           in
        uu____13324 + uu____13325
    | uu____13344 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____13355 =
        let uu____13356 = un_uinst t  in uu____13356.FStar_Syntax_Syntax.n
         in
      match uu____13355 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____13360 -> false
  
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
        let uu____13401 = FStar_Options.set_options t s  in
        match uu____13401 with
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
          ((let uu____13409 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____13409 (fun a236  -> ()));
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
    | FStar_Syntax_Syntax.Tm_delayed uu____13435 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____13463 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____13480 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____13481 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____13482 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____13491) ->
        let uu____13512 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____13512 with
         | (bs1,t2) ->
             let uu____13521 =
               FStar_List.collect
                 (fun uu____13531  ->
                    match uu____13531 with
                    | (b,uu____13539) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____13540 = unbound_variables t2  in
             FStar_List.append uu____13521 uu____13540)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____13561 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____13561 with
         | (bs1,c1) ->
             let uu____13570 =
               FStar_List.collect
                 (fun uu____13580  ->
                    match uu____13580 with
                    | (b,uu____13588) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____13589 = unbound_variables_comp c1  in
             FStar_List.append uu____13570 uu____13589)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____13598 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____13598 with
         | (bs,t2) ->
             let uu____13615 =
               FStar_List.collect
                 (fun uu____13625  ->
                    match uu____13625 with
                    | (b1,uu____13633) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____13634 = unbound_variables t2  in
             FStar_List.append uu____13615 uu____13634)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____13659 =
          FStar_List.collect
            (fun uu____13671  ->
               match uu____13671 with
               | (x,uu____13681) -> unbound_variables x) args
           in
        let uu____13686 = unbound_variables t1  in
        FStar_List.append uu____13659 uu____13686
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____13727 = unbound_variables t1  in
        let uu____13730 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____13745 = FStar_Syntax_Subst.open_branch br  in
                  match uu____13745 with
                  | (p,wopt,t2) ->
                      let uu____13767 = unbound_variables t2  in
                      let uu____13770 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____13767 uu____13770))
           in
        FStar_List.append uu____13727 uu____13730
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____13784) ->
        let uu____13825 = unbound_variables t1  in
        let uu____13828 =
          let uu____13831 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____13862 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____13831 uu____13862  in
        FStar_List.append uu____13825 uu____13828
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____13900 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____13903 =
          let uu____13906 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____13909 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____13914 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____13916 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____13916 with
                 | (uu____13931,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____13906 uu____13909  in
        FStar_List.append uu____13900 uu____13903
    | FStar_Syntax_Syntax.Tm_let ((uu____13933,lbs),t1) ->
        let uu____13950 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____13950 with
         | (lbs1,t2) ->
             let uu____13965 = unbound_variables t2  in
             let uu____13968 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____13975 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____13978 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____13975 uu____13978) lbs1
                in
             FStar_List.append uu____13965 uu____13968)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____13995 = unbound_variables t1  in
        let uu____13998 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____14031  ->
                      match uu____14031 with
                      | (a,uu____14041) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____14046,uu____14047,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____14053,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____14059 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____14066 -> []
          | FStar_Syntax_Syntax.Meta_named uu____14067 -> []  in
        FStar_List.append uu____13995 uu____13998

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____14074) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____14084) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____14094 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____14097 =
          FStar_List.collect
            (fun uu____14109  ->
               match uu____14109 with
               | (a,uu____14119) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____14094 uu____14097
