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
        let uu____1882 = head_and_args' head1  in
        (match uu____1882 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1939 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1961) ->
        FStar_Syntax_Subst.compress t2
    | uu____1966 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1972 =
      let uu____1973 = FStar_Syntax_Subst.compress t  in
      uu____1973.FStar_Syntax_Syntax.n  in
    match uu____1972 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1976,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1998)::uu____1999 ->
                  let pats' = unmeta pats  in
                  let uu____2043 = head_and_args pats'  in
                  (match uu____2043 with
                   | (head1,uu____2059) ->
                       let uu____2080 =
                         let uu____2081 = un_uinst head1  in
                         uu____2081.FStar_Syntax_Syntax.n  in
                       (match uu____2080 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____2085 -> false))
              | uu____2086 -> false)
         | uu____2095 -> false)
    | uu____2096 -> false
  
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
                (fun uu___74_2110  ->
                   match uu___74_2110 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2111 -> false)))
    | uu____2112 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2127) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2137) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2165 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2174 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___83_2186 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___83_2186.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___83_2186.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___83_2186.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___83_2186.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2199  ->
           let uu____2200 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____2200 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___75_2215  ->
            match uu___75_2215 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2216 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2222 -> []
    | FStar_Syntax_Syntax.GTotal uu____2237 -> []
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
    | uu____2272 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2280,uu____2281) ->
        unascribe e2
    | uu____2322 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2374,uu____2375) ->
          ascribe t' k
      | uu____2416 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2442 =
      let uu____2451 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2451  in
    uu____2442 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2510 =
      let uu____2511 = FStar_Syntax_Subst.compress t  in
      uu____2511.FStar_Syntax_Syntax.n  in
    match uu____2510 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2515 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2515
    | uu____2516 -> t
  
let rec unlazy_as_t :
  'Auu____2523 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2523
  =
  fun k  ->
    fun t  ->
      let uu____2534 =
        let uu____2535 = FStar_Syntax_Subst.compress t  in
        uu____2535.FStar_Syntax_Syntax.n  in
      match uu____2534 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.typ = uu____2540;
            FStar_Syntax_Syntax.rng = uu____2541;_}
          when k = k' -> FStar_Dyn.undyn v1
      | uu____2544 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2583 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2583;
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
    let uu____2595 =
      let uu____2608 = unascribe t  in head_and_args' uu____2608  in
    match uu____2595 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2634 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2640 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2646 -> false
  
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
      let equal_if uu___76_2722 = if uu___76_2722 then Equal else Unknown  in
      let equal_iff uu___77_2729 = if uu___77_2729 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2747 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2759) -> NotEqual
        | (uu____2760,NotEqual ) -> NotEqual
        | (Unknown ,uu____2761) -> Unknown
        | (uu____2762,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____2808 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2808
        then
          let uu____2810 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2868  ->
                    match uu____2868 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2894 = eq_tm a1 a2  in
                        eq_inj acc uu____2894) Equal) uu____2810
        else NotEqual  in
      let uu____2896 =
        let uu____2901 =
          let uu____2902 = unmeta t11  in uu____2902.FStar_Syntax_Syntax.n
           in
        let uu____2905 =
          let uu____2906 = unmeta t21  in uu____2906.FStar_Syntax_Syntax.n
           in
        (uu____2901, uu____2905)  in
      match uu____2896 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2911,uu____2912) ->
          let uu____2913 = unlazy t11  in eq_tm uu____2913 t21
      | (uu____2914,FStar_Syntax_Syntax.Tm_lazy uu____2915) ->
          let uu____2916 = unlazy t21  in eq_tm t11 uu____2916
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
            (let uu____2934 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2934)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2947 = eq_tm f g  in
          eq_and uu____2947
            (fun uu____2950  ->
               let uu____2951 = eq_univs_list us vs  in equal_if uu____2951)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2952),uu____2953) -> Unknown
      | (uu____2954,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2955)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2958 = FStar_Const.eq_const c d  in equal_iff uu____2958
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____2960)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____2962))) ->
          let uu____3003 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3003
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3048 =
            let uu____3053 =
              let uu____3054 = un_uinst h1  in
              uu____3054.FStar_Syntax_Syntax.n  in
            let uu____3057 =
              let uu____3058 = un_uinst h2  in
              uu____3058.FStar_Syntax_Syntax.n  in
            (uu____3053, uu____3057)  in
          (match uu____3048 with
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
                 (let uu____3070 =
                    let uu____3071 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3071  in
                  FStar_List.mem uu____3070 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3072 ->
               let uu____3077 = eq_tm h1 h2  in
               eq_and uu____3077 (fun uu____3079  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3184 = FStar_List.zip bs1 bs2  in
            let uu____3247 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3284  ->
                 fun a  ->
                   match uu____3284 with
                   | (b1,b2) ->
                       eq_and a (fun uu____3377  -> branch_matches b1 b2))
              uu____3184 uu____3247
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____3381 = eq_univs u v1  in equal_if uu____3381
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) -> if q1 = q2 then eq_tm t12 t22 else Unknown
      | uu____3395 -> Unknown

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
        | (uu____3478,uu____3479) -> false  in
      let uu____3488 = b1  in
      match uu____3488 with
      | (p1,w1,t1) ->
          let uu____3522 = b2  in
          (match uu____3522 with
           | (p2,w2,t2) ->
               let uu____3556 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3556
               then
                 let uu____3557 =
                   (let uu____3560 = eq_tm t1 t2  in uu____3560 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3569 = eq_tm t11 t21  in
                             uu____3569 = Equal) w1 w2)
                    in
                 (if uu____3557 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3619)::a11,(b,uu____3622)::b1) ->
          let uu____3676 = eq_tm a b  in
          (match uu____3676 with
           | Equal  -> eq_args a11 b1
           | uu____3677 -> Unknown)
      | uu____3678 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3708) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3714,uu____3715) ->
        unrefine t2
    | uu____3756 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3762 =
      let uu____3763 = FStar_Syntax_Subst.compress t  in
      uu____3763.FStar_Syntax_Syntax.n  in
    match uu____3762 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3766 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3782) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____3787 ->
        let uu____3802 =
          let uu____3803 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____3803 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____3802 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3857,uu____3858) ->
        is_uvar t1
    | uu____3899 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3905 =
      let uu____3906 = unrefine t  in uu____3906.FStar_Syntax_Syntax.n  in
    match uu____3905 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3911) -> is_unit t1
    | uu____3916 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3922 =
      let uu____3923 = unrefine t  in uu____3923.FStar_Syntax_Syntax.n  in
    match uu____3922 with
    | FStar_Syntax_Syntax.Tm_type uu____3926 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3929) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3951) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3956,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3974 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____3980 =
      let uu____3981 = FStar_Syntax_Subst.compress e  in
      uu____3981.FStar_Syntax_Syntax.n  in
    match uu____3980 with
    | FStar_Syntax_Syntax.Tm_abs uu____3984 -> true
    | uu____4001 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4007 =
      let uu____4008 = FStar_Syntax_Subst.compress t  in
      uu____4008.FStar_Syntax_Syntax.n  in
    match uu____4007 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4011 -> true
    | uu____4024 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4032) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4038,uu____4039) ->
        pre_typ t2
    | uu____4080 -> t1
  
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
      let uu____4102 =
        let uu____4103 = un_uinst typ1  in uu____4103.FStar_Syntax_Syntax.n
         in
      match uu____4102 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____4158 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____4182 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____4200,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____4207) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____4212,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____4223,uu____4224,uu____4225,uu____4226,uu____4227) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____4237,uu____4238,uu____4239,uu____4240) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____4246,uu____4247,uu____4248,uu____4249,uu____4250) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____4256,uu____4257) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4259,uu____4260) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____4263 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____4264 -> []
    | FStar_Syntax_Syntax.Sig_main uu____4265 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____4278 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___78_4301  ->
    match uu___78_4301 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____4314 'Auu____4315 .
    ('Auu____4314 FStar_Syntax_Syntax.syntax,'Auu____4315)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____4326  ->
    match uu____4326 with | (hd1,uu____4334) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____4347 'Auu____4348 .
    ('Auu____4347 FStar_Syntax_Syntax.syntax,'Auu____4348)
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
      | uu____4439 ->
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
          let uu____4499 = FStar_Ident.range_of_lid l  in
          let uu____4500 =
            let uu____4509 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____4509  in
          uu____4500 FStar_Pervasives_Native.None uu____4499
      | uu____4517 ->
          let e =
            let uu____4529 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____4529 args  in
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
      let uu____4544 =
        let uu____4549 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____4549, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____4544
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
          let uu____4600 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____4600
          then
            let uu____4601 =
              let uu____4606 =
                let uu____4607 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____4607  in
              let uu____4608 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____4606, uu____4608)  in
            FStar_Ident.mk_ident uu____4601
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___84_4611 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___84_4611.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___84_4611.FStar_Syntax_Syntax.sort)
          }  in
        let uu____4612 = mk_field_projector_name_from_ident lid nm  in
        (uu____4612, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4623) -> ses
    | uu____4632 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____4641 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____4652 = FStar_Syntax_Unionfind.find uv  in
      match uu____4652 with
      | FStar_Pervasives_Native.Some uu____4655 ->
          let uu____4656 =
            let uu____4657 =
              let uu____4658 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____4658  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4657  in
          failwith uu____4656
      | uu____4659 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____4734 -> q1 = q2
  
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
              let uu____4779 =
                let uu___85_4780 = rc  in
                let uu____4781 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___85_4780.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____4781;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___85_4780.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____4779
           in
        match bs with
        | [] -> t
        | uu____4796 ->
            let body =
              let uu____4798 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4798  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4828 =
                   let uu____4835 =
                     let uu____4836 =
                       let uu____4853 =
                         let uu____4860 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4860 bs'  in
                       let uu____4871 = close_lopt lopt'  in
                       (uu____4853, t1, uu____4871)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4836  in
                   FStar_Syntax_Syntax.mk uu____4835  in
                 uu____4828 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4887 ->
                 let uu____4894 =
                   let uu____4901 =
                     let uu____4902 =
                       let uu____4919 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4926 = close_lopt lopt  in
                       (uu____4919, body, uu____4926)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4902  in
                   FStar_Syntax_Syntax.mk uu____4901  in
                 uu____4894 FStar_Pervasives_Native.None
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
      | uu____4976 ->
          let uu____4983 =
            let uu____4990 =
              let uu____4991 =
                let uu____5004 = FStar_Syntax_Subst.close_binders bs  in
                let uu____5011 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____5004, uu____5011)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4991  in
            FStar_Syntax_Syntax.mk uu____4990  in
          uu____4983 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____5056 =
        let uu____5057 = FStar_Syntax_Subst.compress t  in
        uu____5057.FStar_Syntax_Syntax.n  in
      match uu____5056 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____5083) ->
               let uu____5092 =
                 let uu____5093 = FStar_Syntax_Subst.compress tres  in
                 uu____5093.FStar_Syntax_Syntax.n  in
               (match uu____5092 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____5128 -> t)
           | uu____5129 -> t)
      | uu____5130 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____5147 =
        let uu____5148 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____5148 t.FStar_Syntax_Syntax.pos  in
      let uu____5149 =
        let uu____5156 =
          let uu____5157 =
            let uu____5164 =
              let uu____5167 =
                let uu____5168 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____5168]  in
              FStar_Syntax_Subst.close uu____5167 t  in
            (b, uu____5164)  in
          FStar_Syntax_Syntax.Tm_refine uu____5157  in
        FStar_Syntax_Syntax.mk uu____5156  in
      uu____5149 FStar_Pervasives_Native.None uu____5147
  
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
        let uu____5235 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____5235 with
         | (bs1,c1) ->
             let uu____5252 = is_total_comp c1  in
             if uu____5252
             then
               let uu____5263 = arrow_formals_comp (comp_result c1)  in
               (match uu____5263 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____5315;
           FStar_Syntax_Syntax.index = uu____5316;
           FStar_Syntax_Syntax.sort = k2;_},uu____5318)
        -> arrow_formals_comp k2
    | uu____5325 ->
        let uu____5326 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____5326)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____5354 = arrow_formals_comp k  in
    match uu____5354 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____5436 =
            let uu___86_5437 = rc  in
            let uu____5438 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___86_5437.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____5438;
              FStar_Syntax_Syntax.residual_flags =
                (uu___86_5437.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____5436
      | uu____5447 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____5479 =
        let uu____5480 =
          let uu____5483 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____5483  in
        uu____5480.FStar_Syntax_Syntax.n  in
      match uu____5479 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____5523 = aux t2 what  in
          (match uu____5523 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____5583 -> ([], t1, abs_body_lcomp)  in
    let uu____5596 = aux t FStar_Pervasives_Native.None  in
    match uu____5596 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____5638 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____5638 with
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
                    | (FStar_Pervasives_Native.None ,uu____5799) -> def
                    | (uu____5810,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____5822) ->
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
            let uu____5908 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____5908 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5937 ->
            let t' = arrow binders c  in
            let uu____5947 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5947 with
             | (uvs1,t'1) ->
                 let uu____5966 =
                   let uu____5967 = FStar_Syntax_Subst.compress t'1  in
                   uu____5967.FStar_Syntax_Syntax.n  in
                 (match uu____5966 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____6008 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____6027 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____6034 -> false
  
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
      let uu____6082 =
        let uu____6083 = pre_typ t  in uu____6083.FStar_Syntax_Syntax.n  in
      match uu____6082 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____6087 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____6098 =
        let uu____6099 = pre_typ t  in uu____6099.FStar_Syntax_Syntax.n  in
      match uu____6098 with
      | FStar_Syntax_Syntax.Tm_fvar uu____6102 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____6104) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6126) ->
          is_constructed_typ t1 lid
      | uu____6131 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____6142 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____6143 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____6144 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____6146) -> get_tycon t2
    | uu____6167 -> FStar_Pervasives_Native.None
  
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
    let uu____6181 =
      let uu____6182 = un_uinst t  in uu____6182.FStar_Syntax_Syntax.n  in
    match uu____6181 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____6186 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____6193 =
        let uu____6196 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____6196  in
      match uu____6193 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____6209 -> false
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
  fun uu____6221  ->
    let u =
      let uu____6227 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_5  -> FStar_Syntax_Syntax.U_unif _0_5)
        uu____6227
       in
    let uu____6244 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____6244, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____6255 = eq_tm a a'  in
      match uu____6255 with | Equal  -> true | uu____6256 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____6259 =
    let uu____6266 =
      let uu____6267 =
        let uu____6268 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____6268
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____6267  in
    FStar_Syntax_Syntax.mk uu____6266  in
  uu____6259 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____6341 =
            let uu____6344 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____6345 =
              let uu____6352 =
                let uu____6353 =
                  let uu____6368 =
                    let uu____6377 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____6384 =
                      let uu____6393 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____6393]  in
                    uu____6377 :: uu____6384  in
                  (tand, uu____6368)  in
                FStar_Syntax_Syntax.Tm_app uu____6353  in
              FStar_Syntax_Syntax.mk uu____6352  in
            uu____6345 FStar_Pervasives_Native.None uu____6344  in
          FStar_Pervasives_Native.Some uu____6341
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____6462 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____6463 =
          let uu____6470 =
            let uu____6471 =
              let uu____6486 =
                let uu____6495 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____6502 =
                  let uu____6511 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____6511]  in
                uu____6495 :: uu____6502  in
              (op_t, uu____6486)  in
            FStar_Syntax_Syntax.Tm_app uu____6471  in
          FStar_Syntax_Syntax.mk uu____6470  in
        uu____6463 FStar_Pervasives_Native.None uu____6462
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____6560 =
      let uu____6567 =
        let uu____6568 =
          let uu____6583 =
            let uu____6592 = FStar_Syntax_Syntax.as_arg phi  in [uu____6592]
             in
          (t_not, uu____6583)  in
        FStar_Syntax_Syntax.Tm_app uu____6568  in
      FStar_Syntax_Syntax.mk uu____6567  in
    uu____6560 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____6777 =
      let uu____6784 =
        let uu____6785 =
          let uu____6800 =
            let uu____6809 = FStar_Syntax_Syntax.as_arg e  in [uu____6809]
             in
          (b2t_v, uu____6800)  in
        FStar_Syntax_Syntax.Tm_app uu____6785  in
      FStar_Syntax_Syntax.mk uu____6784  in
    uu____6777 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____6861 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____6862 =
        let uu____6869 =
          let uu____6870 =
            let uu____6885 =
              let uu____6894 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____6901 =
                let uu____6910 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____6910]  in
              uu____6894 :: uu____6901  in
            (teq, uu____6885)  in
          FStar_Syntax_Syntax.Tm_app uu____6870  in
        FStar_Syntax_Syntax.mk uu____6869  in
      uu____6862 FStar_Pervasives_Native.None uu____6861
  
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
          let uu____6969 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____6970 =
            let uu____6977 =
              let uu____6978 =
                let uu____6993 =
                  let uu____7002 = FStar_Syntax_Syntax.iarg t  in
                  let uu____7009 =
                    let uu____7018 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____7025 =
                      let uu____7034 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____7034]  in
                    uu____7018 :: uu____7025  in
                  uu____7002 :: uu____7009  in
                (eq_inst, uu____6993)  in
              FStar_Syntax_Syntax.Tm_app uu____6978  in
            FStar_Syntax_Syntax.mk uu____6977  in
          uu____6970 FStar_Pervasives_Native.None uu____6969
  
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
        let uu____7101 =
          let uu____7108 =
            let uu____7109 =
              let uu____7124 =
                let uu____7133 = FStar_Syntax_Syntax.iarg t  in
                let uu____7140 =
                  let uu____7149 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____7156 =
                    let uu____7165 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____7165]  in
                  uu____7149 :: uu____7156  in
                uu____7133 :: uu____7140  in
              (t_has_type1, uu____7124)  in
            FStar_Syntax_Syntax.Tm_app uu____7109  in
          FStar_Syntax_Syntax.mk uu____7108  in
        uu____7101 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____7232 =
          let uu____7239 =
            let uu____7240 =
              let uu____7255 =
                let uu____7264 = FStar_Syntax_Syntax.iarg t  in
                let uu____7271 =
                  let uu____7280 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____7280]  in
                uu____7264 :: uu____7271  in
              (t_with_type1, uu____7255)  in
            FStar_Syntax_Syntax.Tm_app uu____7240  in
          FStar_Syntax_Syntax.mk uu____7239  in
        uu____7232 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____7318 =
    let uu____7325 =
      let uu____7326 =
        let uu____7333 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____7333, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____7326  in
    FStar_Syntax_Syntax.mk uu____7325  in
  uu____7318 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____7346 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____7359 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____7370 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____7346 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____7391  -> c0)
  
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
        let uu____7469 =
          let uu____7476 =
            let uu____7477 =
              let uu____7492 =
                let uu____7501 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____7508 =
                  let uu____7517 =
                    let uu____7524 =
                      let uu____7525 =
                        let uu____7526 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____7526]  in
                      abs uu____7525 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____7524  in
                  [uu____7517]  in
                uu____7501 :: uu____7508  in
              (fa, uu____7492)  in
            FStar_Syntax_Syntax.Tm_app uu____7477  in
          FStar_Syntax_Syntax.mk uu____7476  in
        uu____7469 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____7631 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____7631
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____7642 -> true
    | uu____7643 -> false
  
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
          let uu____7688 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____7688, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____7716 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____7716, FStar_Pervasives_Native.None, t2)  in
        let uu____7729 =
          let uu____7730 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____7730  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____7729
  
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
      let uu____7804 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7807 =
        let uu____7816 = FStar_Syntax_Syntax.as_arg p  in [uu____7816]  in
      mk_app uu____7804 uu____7807
  
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
      let uu____7848 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____7851 =
        let uu____7860 = FStar_Syntax_Syntax.as_arg p  in [uu____7860]  in
      mk_app uu____7848 uu____7851
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____7888 = head_and_args t  in
    match uu____7888 with
    | (head1,args) ->
        let uu____7929 =
          let uu____7942 =
            let uu____7943 = un_uinst head1  in
            uu____7943.FStar_Syntax_Syntax.n  in
          (uu____7942, args)  in
        (match uu____7929 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____7960)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____8012 =
                    let uu____8017 =
                      let uu____8018 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____8018]  in
                    FStar_Syntax_Subst.open_term uu____8017 p  in
                  (match uu____8012 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____8059 -> failwith "impossible"  in
                       let uu____8064 =
                         let uu____8065 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____8065
                          in
                       if uu____8064
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____8075 -> FStar_Pervasives_Native.None)
         | uu____8078 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8106 = head_and_args t  in
    match uu____8106 with
    | (head1,args) ->
        let uu____8151 =
          let uu____8164 =
            let uu____8165 = FStar_Syntax_Subst.compress head1  in
            uu____8165.FStar_Syntax_Syntax.n  in
          (uu____8164, args)  in
        (match uu____8151 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____8185;
               FStar_Syntax_Syntax.vars = uu____8186;_},u::[]),(t1,uu____8189)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____8226 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8258 = head_and_args t  in
    match uu____8258 with
    | (head1,args) ->
        let uu____8303 =
          let uu____8316 =
            let uu____8317 = FStar_Syntax_Subst.compress head1  in
            uu____8317.FStar_Syntax_Syntax.n  in
          (uu____8316, args)  in
        (match uu____8303 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____8337;
               FStar_Syntax_Syntax.vars = uu____8338;_},u::[]),(t1,uu____8341)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____8378 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8402 = let uu____8417 = unmeta t  in head_and_args uu____8417
       in
    match uu____8402 with
    | (head1,uu____8419) ->
        let uu____8440 =
          let uu____8441 = un_uinst head1  in
          uu____8441.FStar_Syntax_Syntax.n  in
        (match uu____8440 with
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
         | uu____8445 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8463 =
      let uu____8474 =
        let uu____8475 = FStar_Syntax_Subst.compress t  in
        uu____8475.FStar_Syntax_Syntax.n  in
      match uu____8474 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____8578 =
            let uu____8587 =
              let uu____8588 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____8588  in
            (b, uu____8587)  in
          FStar_Pervasives_Native.Some uu____8578
      | uu____8601 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____8463
      (fun uu____8633  ->
         match uu____8633 with
         | (b,c) ->
             let uu____8662 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____8662 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____8709 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____8736 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8736
  
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
    match projectee with | QAll _0 -> true | uu____8784 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____8822 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____8858 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____8895) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____8907) ->
          unmeta_monadic t
      | uu____8920 -> f2  in
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
      let aux f2 uu____9004 =
        match uu____9004 with
        | (lid,arity) ->
            let uu____9013 =
              let uu____9028 = unmeta_monadic f2  in head_and_args uu____9028
               in
            (match uu____9013 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____9054 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____9054
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____9123 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____9123)
      | uu____9134 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____9189 = head_and_args t1  in
        match uu____9189 with
        | (t2,args) ->
            let uu____9236 = un_uinst t2  in
            let uu____9237 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9268  ->
                      match uu____9268 with
                      | (t3,imp) ->
                          let uu____9279 = unascribe t3  in (uu____9279, imp)))
               in
            (uu____9236, uu____9237)
         in
      let rec aux qopt out t1 =
        let uu____9320 = let uu____9341 = flat t1  in (qopt, uu____9341)  in
        match uu____9320 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____9376;
                 FStar_Syntax_Syntax.vars = uu____9377;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____9380);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____9381;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____9382;_},uu____9383)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____9460;
                 FStar_Syntax_Syntax.vars = uu____9461;_},uu____9462::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____9465);
                  FStar_Syntax_Syntax.pos = uu____9466;
                  FStar_Syntax_Syntax.vars = uu____9467;_},uu____9468)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9556;
               FStar_Syntax_Syntax.vars = uu____9557;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____9560);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____9561;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____9562;_},uu____9563)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9634 =
              let uu____9637 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9637  in
            aux uu____9634 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____9643;
               FStar_Syntax_Syntax.vars = uu____9644;_},uu____9645::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____9648);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____9649;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____9650;_},uu____9651)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____9734 =
              let uu____9737 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____9737  in
            aux uu____9734 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____9743) ->
            let bs = FStar_List.rev out  in
            let uu____9785 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____9785 with
             | (bs1,t2) ->
                 let uu____9794 = patterns t2  in
                 (match uu____9794 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____9836 -> FStar_Pervasives_Native.None  in
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
      let uu____9908 = un_squash t  in
      FStar_Util.bind_opt uu____9908
        (fun t1  ->
           let uu____9924 = head_and_args' t1  in
           match uu____9924 with
           | (hd1,args) ->
               let uu____9957 =
                 let uu____9962 =
                   let uu____9963 = un_uinst hd1  in
                   uu____9963.FStar_Syntax_Syntax.n  in
                 (uu____9962, (FStar_List.length args))  in
               (match uu____9957 with
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
                | uu____9982 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____10011 = un_squash t  in
      FStar_Util.bind_opt uu____10011
        (fun t1  ->
           let uu____10026 = arrow_one t1  in
           match uu____10026 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____10041 =
                 let uu____10042 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____10042  in
               if uu____10041
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____10049 = comp_to_comp_typ_nouniv c  in
                    uu____10049.FStar_Syntax_Syntax.result_typ  in
                  let uu____10050 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____10050
                  then
                    let uu____10053 = patterns q  in
                    match uu____10053 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____10105 =
                       let uu____10106 =
                         let uu____10111 =
                           let uu____10112 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____10119 =
                             let uu____10128 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____10128]  in
                           uu____10112 :: uu____10119  in
                         (FStar_Parser_Const.imp_lid, uu____10111)  in
                       BaseConn uu____10106  in
                     FStar_Pervasives_Native.Some uu____10105))
           | uu____10153 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____10161 = un_squash t  in
      FStar_Util.bind_opt uu____10161
        (fun t1  ->
           let uu____10192 = head_and_args' t1  in
           match uu____10192 with
           | (hd1,args) ->
               let uu____10225 =
                 let uu____10238 =
                   let uu____10239 = un_uinst hd1  in
                   uu____10239.FStar_Syntax_Syntax.n  in
                 (uu____10238, args)  in
               (match uu____10225 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____10254)::(a2,uu____10256)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____10291 =
                      let uu____10292 = FStar_Syntax_Subst.compress a2  in
                      uu____10292.FStar_Syntax_Syntax.n  in
                    (match uu____10291 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____10299) ->
                         let uu____10326 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____10326 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____10365 -> failwith "impossible"  in
                              let uu____10370 = patterns q1  in
                              (match uu____10370 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____10421 -> FStar_Pervasives_Native.None)
                | uu____10422 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____10443 = destruct_sq_forall phi  in
          (match uu____10443 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____10457 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____10463 = destruct_sq_exists phi  in
          (match uu____10463 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____10477 -> f1)
      | uu____10480 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____10484 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____10484
      (fun uu____10489  ->
         let uu____10490 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____10490
           (fun uu____10495  ->
              let uu____10496 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____10496
                (fun uu____10501  ->
                   let uu____10502 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____10502
                     (fun uu____10507  ->
                        let uu____10508 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____10508
                          (fun uu____10512  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____10524 =
      let uu____10525 = FStar_Syntax_Subst.compress t  in
      uu____10525.FStar_Syntax_Syntax.n  in
    match uu____10524 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____10532) ->
        let uu____10559 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____10559 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____10585 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____10585
             then
               let uu____10588 =
                 let uu____10597 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____10597]  in
               mk_app t uu____10588
             else e1)
    | uu____10617 ->
        let uu____10618 =
          let uu____10627 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____10627]  in
        mk_app t uu____10618
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____10662 =
            let uu____10667 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____10667  in
          let uu____10668 =
            let uu____10669 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____10669  in
          let uu____10672 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____10662 a.FStar_Syntax_Syntax.action_univs uu____10668
            FStar_Parser_Const.effect_Tot_lid uu____10672 [] pos
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
    let uu____10695 =
      let uu____10702 =
        let uu____10703 =
          let uu____10718 =
            let uu____10727 = FStar_Syntax_Syntax.as_arg t  in [uu____10727]
             in
          (reify_, uu____10718)  in
        FStar_Syntax_Syntax.Tm_app uu____10703  in
      FStar_Syntax_Syntax.mk uu____10702  in
    uu____10695 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10765 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____10791 = unfold_lazy i  in delta_qualifier uu____10791
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____10793 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____10794 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____10795 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____10818 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____10833 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____10834 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____10841 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____10842 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____10856) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____10861;
           FStar_Syntax_Syntax.index = uu____10862;
           FStar_Syntax_Syntax.sort = t2;_},uu____10864)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____10872) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____10878,uu____10879) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____10921) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____10942,t2,uu____10944) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____10965,t2) -> delta_qualifier t2
  
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
    let uu____10996 = delta_qualifier t  in incr_delta_depth uu____10996
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11002 =
      let uu____11003 = FStar_Syntax_Subst.compress t  in
      uu____11003.FStar_Syntax_Syntax.n  in
    match uu____11002 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____11006 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____11020 =
      let uu____11035 = unmeta e  in head_and_args uu____11035  in
    match uu____11020 with
    | (head1,args) ->
        let uu____11062 =
          let uu____11075 =
            let uu____11076 = un_uinst head1  in
            uu____11076.FStar_Syntax_Syntax.n  in
          (uu____11075, args)  in
        (match uu____11062 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11092) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____11112::(hd1,uu____11114)::(tl1,uu____11116)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____11163 =
               let uu____11166 =
                 let uu____11169 = list_elements tl1  in
                 FStar_Util.must uu____11169  in
               hd1 :: uu____11166  in
             FStar_Pervasives_Native.Some uu____11163
         | uu____11178 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____11200 .
    ('Auu____11200 -> 'Auu____11200) ->
      'Auu____11200 Prims.list -> 'Auu____11200 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____11225 = f a  in [uu____11225]
      | x::xs -> let uu____11230 = apply_last f xs  in x :: uu____11230
  
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
          let uu____11276 =
            let uu____11283 =
              let uu____11284 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____11284  in
            FStar_Syntax_Syntax.mk uu____11283  in
          uu____11276 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____11301 =
            let uu____11306 =
              let uu____11307 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____11307
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____11306 args  in
          uu____11301 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____11323 =
            let uu____11328 =
              let uu____11329 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____11329
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____11328 args  in
          uu____11323 FStar_Pervasives_Native.None pos  in
        let uu____11332 =
          let uu____11333 =
            let uu____11334 = FStar_Syntax_Syntax.iarg typ  in [uu____11334]
             in
          nil uu____11333 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____11362 =
                 let uu____11363 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____11370 =
                   let uu____11379 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____11386 =
                     let uu____11395 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____11395]  in
                   uu____11379 :: uu____11386  in
                 uu____11363 :: uu____11370  in
               cons1 uu____11362 t.FStar_Syntax_Syntax.pos) l uu____11332
  
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
    fun uu____11453  ->
      match uu____11453 with
      | (gamma,bs,t) ->
          let ctx_u =
            let uu____11496 = FStar_Syntax_Unionfind.from_id id1  in
            {
              FStar_Syntax_Syntax.ctx_uvar_head = uu____11496;
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
        | uu____11589 -> false
  
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
          | uu____11696 -> false
  
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
        | uu____11851 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____11885 = FStar_ST.op_Bang debug_term_eq  in
          if uu____11885
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
        let t11 = let uu____12073 = unmeta_safe t1  in canon_app uu____12073
           in
        let t21 = let uu____12079 = unmeta_safe t2  in canon_app uu____12079
           in
        let uu____12082 =
          let uu____12087 =
            let uu____12088 =
              let uu____12091 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____12091  in
            uu____12088.FStar_Syntax_Syntax.n  in
          let uu____12092 =
            let uu____12093 =
              let uu____12096 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____12096  in
            uu____12093.FStar_Syntax_Syntax.n  in
          (uu____12087, uu____12092)  in
        match uu____12082 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____12097,uu____12098) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12105,FStar_Syntax_Syntax.Tm_uinst uu____12106) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____12113,uu____12114) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12139,FStar_Syntax_Syntax.Tm_delayed uu____12140) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____12165,uu____12166) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____12193,FStar_Syntax_Syntax.Tm_ascribed uu____12194) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____12227 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____12227
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____12230 = FStar_Const.eq_const c1 c2  in
            check "const" uu____12230
        | (FStar_Syntax_Syntax.Tm_type
           uu____12231,FStar_Syntax_Syntax.Tm_type uu____12232) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____12281 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____12281) &&
              (let uu____12287 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____12287)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____12326 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____12326) &&
              (let uu____12332 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____12332)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____12346 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____12346)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____12393 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____12393) &&
              (let uu____12395 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____12395)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____12480 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____12480) &&
              (let uu____12482 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____12482)
        | (FStar_Syntax_Syntax.Tm_lazy uu____12497,uu____12498) ->
            let uu____12499 =
              let uu____12500 = unlazy t11  in
              term_eq_dbg dbg uu____12500 t21  in
            check "lazy_l" uu____12499
        | (uu____12501,FStar_Syntax_Syntax.Tm_lazy uu____12502) ->
            let uu____12503 =
              let uu____12504 = unlazy t21  in
              term_eq_dbg dbg t11 uu____12504  in
            check "lazy_r" uu____12503
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____12540 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____12540))
              &&
              (let uu____12542 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____12542)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____12544),FStar_Syntax_Syntax.Tm_uvar (u2,uu____12546)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (check "tm_quoted qi" (qi1 = qi2)) &&
              (let uu____12610 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____12610)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____12637 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____12637) &&
                   (let uu____12639 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____12639)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____12656 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____12656) &&
                    (let uu____12658 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____12658))
                   &&
                   (let uu____12660 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____12660)
             | uu____12661 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____12666) -> fail "unk"
        | (uu____12667,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____12668,uu____12669) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____12670,uu____12671) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____12672,uu____12673) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____12674,uu____12675) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____12676,uu____12677) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____12678,uu____12679) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____12696,uu____12697) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____12710,uu____12711) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____12718,uu____12719) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____12734,uu____12735) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____12758,uu____12759) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____12772,uu____12773) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____12788,uu____12789) ->
            fail "bottom"
        | (uu____12796,FStar_Syntax_Syntax.Tm_bvar uu____12797) ->
            fail "bottom"
        | (uu____12798,FStar_Syntax_Syntax.Tm_name uu____12799) ->
            fail "bottom"
        | (uu____12800,FStar_Syntax_Syntax.Tm_fvar uu____12801) ->
            fail "bottom"
        | (uu____12802,FStar_Syntax_Syntax.Tm_constant uu____12803) ->
            fail "bottom"
        | (uu____12804,FStar_Syntax_Syntax.Tm_type uu____12805) ->
            fail "bottom"
        | (uu____12806,FStar_Syntax_Syntax.Tm_abs uu____12807) ->
            fail "bottom"
        | (uu____12824,FStar_Syntax_Syntax.Tm_arrow uu____12825) ->
            fail "bottom"
        | (uu____12838,FStar_Syntax_Syntax.Tm_refine uu____12839) ->
            fail "bottom"
        | (uu____12846,FStar_Syntax_Syntax.Tm_app uu____12847) ->
            fail "bottom"
        | (uu____12862,FStar_Syntax_Syntax.Tm_match uu____12863) ->
            fail "bottom"
        | (uu____12886,FStar_Syntax_Syntax.Tm_let uu____12887) ->
            fail "bottom"
        | (uu____12900,FStar_Syntax_Syntax.Tm_uvar uu____12901) ->
            fail "bottom"
        | (uu____12916,FStar_Syntax_Syntax.Tm_meta uu____12917) ->
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
               let uu____12944 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____12944)
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
               let uu____12965 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____12965)
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
        ((let uu____12985 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____12985) &&
           (let uu____12987 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____12987))
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
    fun uu____12992  ->
      fun uu____12993  ->
        match (uu____12992, uu____12993) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____13118 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____13118) &&
               (let uu____13120 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____13120))
              &&
              (let uu____13122 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____13137 -> false  in
               check "branch when" uu____13122)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____13151 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____13151) &&
           (let uu____13157 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____13157))
          &&
          (let uu____13159 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____13159)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____13171 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____13171 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13224 ->
        let uu____13249 =
          let uu____13250 = FStar_Syntax_Subst.compress t  in
          sizeof uu____13250  in
        (Prims.parse_int "1") + uu____13249
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____13252 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____13252
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____13254 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____13254
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____13261 = sizeof t1  in (FStar_List.length us) + uu____13261
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____13264) ->
        let uu____13285 = sizeof t1  in
        let uu____13286 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____13297  ->
                 match uu____13297 with
                 | (bv,uu____13303) ->
                     let uu____13304 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____13304) (Prims.parse_int "0") bs
           in
        uu____13285 + uu____13286
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____13327 = sizeof hd1  in
        let uu____13328 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____13339  ->
                 match uu____13339 with
                 | (arg,uu____13345) ->
                     let uu____13346 = sizeof arg  in acc + uu____13346)
            (Prims.parse_int "0") args
           in
        uu____13327 + uu____13328
    | uu____13347 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____13358 =
        let uu____13359 = un_uinst t  in uu____13359.FStar_Syntax_Syntax.n
         in
      match uu____13358 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____13363 -> false
  
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
        let uu____13404 = FStar_Options.set_options t s  in
        match uu____13404 with
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
          ((let uu____13412 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____13412 (fun a236  -> ()));
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
    | FStar_Syntax_Syntax.Tm_delayed uu____13438 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____13466 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____13483 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____13484 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____13485 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____13494) ->
        let uu____13515 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____13515 with
         | (bs1,t2) ->
             let uu____13524 =
               FStar_List.collect
                 (fun uu____13534  ->
                    match uu____13534 with
                    | (b,uu____13542) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____13543 = unbound_variables t2  in
             FStar_List.append uu____13524 uu____13543)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____13564 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____13564 with
         | (bs1,c1) ->
             let uu____13573 =
               FStar_List.collect
                 (fun uu____13583  ->
                    match uu____13583 with
                    | (b,uu____13591) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____13592 = unbound_variables_comp c1  in
             FStar_List.append uu____13573 uu____13592)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____13601 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____13601 with
         | (bs,t2) ->
             let uu____13618 =
               FStar_List.collect
                 (fun uu____13628  ->
                    match uu____13628 with
                    | (b1,uu____13636) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____13637 = unbound_variables t2  in
             FStar_List.append uu____13618 uu____13637)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____13662 =
          FStar_List.collect
            (fun uu____13674  ->
               match uu____13674 with
               | (x,uu____13684) -> unbound_variables x) args
           in
        let uu____13689 = unbound_variables t1  in
        FStar_List.append uu____13662 uu____13689
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____13730 = unbound_variables t1  in
        let uu____13733 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____13748 = FStar_Syntax_Subst.open_branch br  in
                  match uu____13748 with
                  | (p,wopt,t2) ->
                      let uu____13770 = unbound_variables t2  in
                      let uu____13773 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____13770 uu____13773))
           in
        FStar_List.append uu____13730 uu____13733
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____13787) ->
        let uu____13828 = unbound_variables t1  in
        let uu____13831 =
          let uu____13834 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____13865 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____13834 uu____13865  in
        FStar_List.append uu____13828 uu____13831
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____13903 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____13906 =
          let uu____13909 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____13912 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____13917 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____13919 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____13919 with
                 | (uu____13934,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____13909 uu____13912  in
        FStar_List.append uu____13903 uu____13906
    | FStar_Syntax_Syntax.Tm_let ((uu____13936,lbs),t1) ->
        let uu____13953 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____13953 with
         | (lbs1,t2) ->
             let uu____13968 = unbound_variables t2  in
             let uu____13971 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____13978 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____13981 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____13978 uu____13981) lbs1
                in
             FStar_List.append uu____13968 uu____13971)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____13998 = unbound_variables t1  in
        let uu____14001 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____14034  ->
                      match uu____14034 with
                      | (a,uu____14044) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____14049,uu____14050,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____14056,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____14062 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____14069 -> []
          | FStar_Syntax_Syntax.Meta_named uu____14070 -> []  in
        FStar_List.append uu____13998 uu____14001

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____14077) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____14087) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____14097 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____14100 =
          FStar_List.collect
            (fun uu____14112  ->
               match uu____14112 with
               | (a,uu____14122) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____14097 uu____14100
