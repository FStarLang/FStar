open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____26 = FStar_ST.op_Bang tts_f  in
    match uu____26 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____90 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____90 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____97 =
      let uu____100 =
        let uu____103 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
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
        Prims.int_zero
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____121 .
    (FStar_Syntax_Syntax.bv * 'Auu____121) ->
      (FStar_Syntax_Syntax.term * 'Auu____121)
  =
  fun uu____134  ->
    match uu____134 with
    | (b,imp) ->
        let uu____141 = FStar_Syntax_Syntax.bv_to_name b  in (uu____141, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____193 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____193
            then []
            else (let uu____212 = arg_of_non_null_binder b  in [uu____212])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____247 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____329 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____329
              then
                let b1 =
                  let uu____355 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____355, (FStar_Pervasives_Native.snd b))  in
                let uu____362 = arg_of_non_null_binder b1  in (b1, uu____362)
              else
                (let uu____385 = arg_of_non_null_binder b  in (b, uu____385))))
       in
    FStar_All.pipe_right uu____247 FStar_List.unzip
  
let (name_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____519 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____519
              then
                let uu____528 = b  in
                match uu____528 with
                | (a,imp) ->
                    let b1 =
                      let uu____548 =
                        let uu____550 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____550  in
                      FStar_Ident.id_of_text uu____548  in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = Prims.int_zero;
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
        let uu____595 =
          let uu____602 =
            let uu____603 =
              let uu____618 = name_binders binders  in (uu____618, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____603  in
          FStar_Syntax_Syntax.mk uu____602  in
        uu____595 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____637 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____674  ->
            match uu____674 with
            | (t,imp) ->
                let uu____685 =
                  let uu____686 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____686
                   in
                (uu____685, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____741  ->
            match uu____741 with
            | (t,imp) ->
                let uu____758 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____758, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____771 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____771
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____783 . 'Auu____783 -> 'Auu____783 Prims.list =
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
          (fun uu____909  ->
             fun uu____910  ->
               match (uu____909, uu____910) with
               | ((x,uu____936),(y,uu____938)) ->
                   let uu____959 =
                     let uu____966 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____966)  in
                   FStar_Syntax_Syntax.NT uu____959) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____982) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____988,uu____989) -> unmeta e2
    | uu____1030 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____1044 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____1051 -> e1
         | uu____1060 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1062,uu____1063) ->
        unmeta_safe e2
    | uu____1104 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_name uu____1123 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_unif uu____1126 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_zero  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1140 = univ_kernel u1  in
        (match uu____1140 with | (k,n1) -> (k, (n1 + Prims.int_one)))
    | FStar_Syntax_Syntax.U_max uu____1157 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____1166 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____1181 = univ_kernel u  in FStar_Pervasives_Native.snd uu____1181
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____1201,uu____1202) ->
          failwith "Impossible: compare_univs"
      | (uu____1206,FStar_Syntax_Syntax.U_bvar uu____1207) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.int_zero
      | (FStar_Syntax_Syntax.U_unknown ,uu____1212) -> ~- Prims.int_one
      | (uu____1214,FStar_Syntax_Syntax.U_unknown ) -> Prims.int_one
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.int_zero
      | (FStar_Syntax_Syntax.U_zero ,uu____1217) -> ~- Prims.int_one
      | (uu____1219,FStar_Syntax_Syntax.U_zero ) -> Prims.int_one
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____1223,FStar_Syntax_Syntax.U_unif
         uu____1224) -> ~- Prims.int_one
      | (FStar_Syntax_Syntax.U_unif uu____1234,FStar_Syntax_Syntax.U_name
         uu____1235) -> Prims.int_one
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____1263 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____1265 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____1263 - uu____1265
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____1283 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____1283
                 (fun uu____1299  ->
                    match uu____1299 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> Prims.int_zero
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> Prims.int_zero
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1327,uu____1328) -> ~- Prims.int_one
      | (uu____1332,FStar_Syntax_Syntax.U_max uu____1333) -> Prims.int_one
      | uu____1337 ->
          let uu____1342 = univ_kernel u1  in
          (match uu____1342 with
           | (k1,n1) ->
               let uu____1353 = univ_kernel u2  in
               (match uu____1353 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = Prims.int_zero then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1384 = compare_univs u1 u2  in uu____1384 = Prims.int_zero
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1403 =
        let uu____1404 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1404;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1403
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1424 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1433 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1456 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1465 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1492 =
          let uu____1493 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1493  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1492;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1522 =
          let uu____1523 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1523  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1522;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
  
let (comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    fun f  ->
      let uu___229_1559 = c  in
      let uu____1560 =
        let uu____1561 =
          let uu___231_1562 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___231_1562.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___231_1562.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___231_1562.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___231_1562.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1561  in
      {
        FStar_Syntax_Syntax.n = uu____1560;
        FStar_Syntax_Syntax.pos = (uu___229_1559.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___229_1559.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1588 -> c
        | FStar_Syntax_Syntax.GTotal uu____1597 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___243_1608 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___243_1608.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___243_1608.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___243_1608.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___243_1608.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___246_1609 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___246_1609.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___246_1609.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1612  ->
           let uu____1613 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1613)
  
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
    | uu____1653 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1668 -> true
    | FStar_Syntax_Syntax.GTotal uu____1678 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1703  ->
               match uu___0_1703 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1707 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___1_1720  ->
               match uu___1_1720 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1724 -> false)))
  
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
            (fun uu___2_1737  ->
               match uu___2_1737 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1741 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___3_1758  ->
            match uu___3_1758 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1762 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___4_1775  ->
            match uu___4_1775 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1779 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1811 -> true
    | FStar_Syntax_Syntax.GTotal uu____1821 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___5_1836  ->
                   match uu___5_1836 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1839 -> false)))
  
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
            (fun uu___6_1884  ->
               match uu___6_1884 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1887 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1903 =
      let uu____1904 = FStar_Syntax_Subst.compress t  in
      uu____1904.FStar_Syntax_Syntax.n  in
    match uu____1903 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1908,c) -> is_pure_or_ghost_comp c
    | uu____1930 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1945 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1954 =
      let uu____1955 = FStar_Syntax_Subst.compress t  in
      uu____1955.FStar_Syntax_Syntax.n  in
    match uu____1954 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1959,c) -> is_lemma_comp c
    | uu____1981 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1989 =
      let uu____1990 = FStar_Syntax_Subst.compress t  in
      uu____1990.FStar_Syntax_Syntax.n  in
    match uu____1989 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1994) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____2020) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2057,t1,uu____2059) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2085,uu____2086) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2128) -> head_of t1
    | uu____2133 -> t
  
let (head_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list))
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____2211 -> (t1, [])
  
let rec (head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____2293 = head_and_args' head1  in
        (match uu____2293 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____2362 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2389) ->
        FStar_Syntax_Subst.compress t2
    | uu____2394 -> t1
  
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
                (fun uu___7_2412  ->
                   match uu___7_2412 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2415 -> false)))
    | uu____2417 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2434) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2444) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2473 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2482 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___399_2494 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___399_2494.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___399_2494.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___399_2494.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___399_2494.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2508  ->
           let uu____2509 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____2509 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___8_2527  ->
            match uu___8_2527 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2531 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2539 -> []
    | FStar_Syntax_Syntax.GTotal uu____2556 -> []
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
    | uu____2600 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2610,uu____2611) ->
        unascribe e2
    | uu____2652 -> e1
  
let rec (ascribe :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.comp'
                                                             FStar_Syntax_Syntax.syntax)
      FStar_Util.either * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun k  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2705,uu____2706) ->
          ascribe t' k
      | uu____2747 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2774 =
      let uu____2783 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2783  in
    uu____2774 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2839 =
      let uu____2840 = FStar_Syntax_Subst.compress t  in
      uu____2840.FStar_Syntax_Syntax.n  in
    match uu____2839 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2844 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2844
    | uu____2845 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2852 =
      let uu____2853 = FStar_Syntax_Subst.compress t  in
      uu____2853.FStar_Syntax_Syntax.n  in
    match uu____2852 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2857 ->
             let uu____2866 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____2866
         | uu____2867 -> t)
    | uu____2868 -> t
  
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
      | (FStar_Syntax_Syntax.Lazy_goal ,FStar_Syntax_Syntax.Lazy_goal ) ->
          true
      | (FStar_Syntax_Syntax.Lazy_sigelt ,FStar_Syntax_Syntax.Lazy_sigelt )
          -> true
      | (FStar_Syntax_Syntax.Lazy_uvar ,FStar_Syntax_Syntax.Lazy_uvar ) ->
          true
      | uu____2892 -> false
  
let rec unlazy_as_t :
  'Auu____2905 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2905
  =
  fun k  ->
    fun t  ->
      let uu____2916 =
        let uu____2917 = FStar_Syntax_Subst.compress t  in
        uu____2917.FStar_Syntax_Syntax.n  in
      match uu____2916 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2922;
            FStar_Syntax_Syntax.rng = uu____2923;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____2926 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2967 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2967;
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
    let uu____2980 =
      let uu____2995 = unascribe t  in head_and_args' uu____2995  in
    match uu____2980 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____3029 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____3040 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____3051 -> false
  
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
let (eq_inj : eq_result -> eq_result -> eq_result) =
  fun f  ->
    fun g  ->
      match (f, g) with
      | (Equal ,Equal ) -> Equal
      | (NotEqual ,uu____3101) -> NotEqual
      | (uu____3102,NotEqual ) -> NotEqual
      | (Unknown ,uu____3103) -> Unknown
      | (uu____3104,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___9_3225 = if uu___9_3225 then Equal else Unknown  in
      let equal_iff uu___10_3236 = if uu___10_3236 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____3257 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3279 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3279
        then
          let uu____3283 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3360  ->
                    match uu____3360 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3401 = eq_tm a1 a2  in
                        eq_inj acc uu____3401) Equal) uu____3283
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3415 =
          let uu____3432 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3432 head_and_args  in
        match uu____3415 with
        | (head1,args1) ->
            let uu____3485 =
              let uu____3502 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3502 head_and_args  in
            (match uu____3485 with
             | (head2,args2) ->
                 let uu____3555 =
                   let uu____3560 =
                     let uu____3561 = un_uinst head1  in
                     uu____3561.FStar_Syntax_Syntax.n  in
                   let uu____3564 =
                     let uu____3565 = un_uinst head2  in
                     uu____3565.FStar_Syntax_Syntax.n  in
                   (uu____3560, uu____3564)  in
                 (match uu____3555 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     f,FStar_Syntax_Syntax.Tm_fvar g) when
                      (f.FStar_Syntax_Syntax.fv_qual =
                         (FStar_Pervasives_Native.Some
                            FStar_Syntax_Syntax.Data_ctor))
                        &&
                        (g.FStar_Syntax_Syntax.fv_qual =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Data_ctor))
                      -> FStar_Pervasives_Native.Some (f, args1, g, args2)
                  | uu____3592 -> FStar_Pervasives_Native.None))
         in
      let uu____3605 =
        let uu____3610 =
          let uu____3611 = unmeta t11  in uu____3611.FStar_Syntax_Syntax.n
           in
        let uu____3614 =
          let uu____3615 = unmeta t21  in uu____3615.FStar_Syntax_Syntax.n
           in
        (uu____3610, uu____3614)  in
      match uu____3605 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3621,uu____3622) ->
          let uu____3623 = unlazy t11  in eq_tm uu____3623 t21
      | (uu____3624,FStar_Syntax_Syntax.Tm_lazy uu____3625) ->
          let uu____3626 = unlazy t21  in eq_tm t11 uu____3626
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____3629 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3653 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3653
            (fun uu____3701  ->
               match uu____3701 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3716 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3716
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3730 = eq_tm f g  in
          eq_and uu____3730
            (fun uu____3733  ->
               let uu____3734 = eq_univs_list us vs  in equal_if uu____3734)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3736),uu____3737) -> Unknown
      | (uu____3738,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3739)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3742 = FStar_Const.eq_const c d  in equal_iff uu____3742
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3745)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3747))) ->
          let uu____3776 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3776
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3830 =
            let uu____3835 =
              let uu____3836 = un_uinst h1  in
              uu____3836.FStar_Syntax_Syntax.n  in
            let uu____3839 =
              let uu____3840 = un_uinst h2  in
              uu____3840.FStar_Syntax_Syntax.n  in
            (uu____3835, uu____3839)  in
          (match uu____3830 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3846 =
                    let uu____3848 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3848  in
                  FStar_List.mem uu____3846 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3850 ->
               let uu____3855 = eq_tm h1 h2  in
               eq_and uu____3855 (fun uu____3857  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3963 = FStar_List.zip bs1 bs2  in
            let uu____4026 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____4063  ->
                 fun a  ->
                   match uu____4063 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4156  -> branch_matches b1 b2))
              uu____3963 uu____4026
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____4161 = eq_univs u v1  in equal_if uu____4161
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____4175 = eq_quoteinfo q1 q2  in
          eq_and uu____4175 (fun uu____4177  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____4190 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4190 (fun uu____4192  -> eq_tm phi1 phi2)
      | uu____4193 -> Unknown

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
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) Prims.list -> eq_result)
  =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ([],uu____4265) -> NotEqual
      | (uu____4296,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____4388 = eq_tm t1 t2  in
             match uu____4388 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4389 = eq_antiquotes a11 a21  in
                 (match uu____4389 with
                  | NotEqual  -> NotEqual
                  | uu____4390 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____4405) -> NotEqual
      | (uu____4412,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4442 -> NotEqual

and (branch_matches :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) -> eq_result)
  =
  fun b1  ->
    fun b2  ->
      let related_by f o1 o2 =
        match (o1, o2) with
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            true
        | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y) ->
            f x y
        | (uu____4534,uu____4535) -> false  in
      let uu____4545 = b1  in
      match uu____4545 with
      | (p1,w1,t1) ->
          let uu____4579 = b2  in
          (match uu____4579 with
           | (p2,w2,t2) ->
               let uu____4613 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4613
               then
                 let uu____4616 =
                   (let uu____4620 = eq_tm t1 t2  in uu____4620 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4629 = eq_tm t11 t21  in
                             uu____4629 = Equal) w1 w2)
                    in
                 (if uu____4616 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4694)::a11,(b,uu____4697)::b1) ->
          let uu____4771 = eq_tm a b  in
          (match uu____4771 with
           | Equal  -> eq_args a11 b1
           | uu____4772 -> Unknown)
      | uu____4773 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4809) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4815,uu____4816) ->
        unrefine t2
    | uu____4857 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4865 =
      let uu____4866 = FStar_Syntax_Subst.compress t  in
      uu____4866.FStar_Syntax_Syntax.n  in
    match uu____4865 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4870 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4885) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4890 ->
        let uu____4907 =
          let uu____4908 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4908 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4907 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4971,uu____4972) ->
        is_uvar t1
    | uu____5013 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5022 =
      let uu____5023 = unrefine t  in uu____5023.FStar_Syntax_Syntax.n  in
    match uu____5022 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____5029) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5055) -> is_unit t1
    | uu____5060 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5069 =
      let uu____5070 = FStar_Syntax_Subst.compress t  in
      uu____5070.FStar_Syntax_Syntax.n  in
    match uu____5069 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5075 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5084 =
      let uu____5085 = unrefine t  in uu____5085.FStar_Syntax_Syntax.n  in
    match uu____5084 with
    | FStar_Syntax_Syntax.Tm_type uu____5089 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____5093) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5119) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____5124,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____5146 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5155 =
      let uu____5156 = FStar_Syntax_Subst.compress e  in
      uu____5156.FStar_Syntax_Syntax.n  in
    match uu____5155 with
    | FStar_Syntax_Syntax.Tm_abs uu____5160 -> true
    | uu____5180 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5189 =
      let uu____5190 = FStar_Syntax_Subst.compress t  in
      uu____5190.FStar_Syntax_Syntax.n  in
    match uu____5189 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5194 -> true
    | uu____5210 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5220) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5226,uu____5227) ->
        pre_typ t2
    | uu____5268 -> t1
  
let (destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list FStar_Pervasives_Native.option)
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ  in
      let uu____5293 =
        let uu____5294 = un_uinst typ1  in uu____5294.FStar_Syntax_Syntax.n
         in
      match uu____5293 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5359 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5389 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5410,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5417) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5422,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5433,uu____5434,uu____5435,uu____5436,uu____5437) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5447,uu____5448,uu____5449,uu____5450) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5456,uu____5457,uu____5458,uu____5459,uu____5460) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5468,uu____5469) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5471,uu____5472) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5475 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5476 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5477 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5491 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___11_5517  ->
    match uu___11_5517 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5531 'Auu____5532 .
    ('Auu____5531 FStar_Syntax_Syntax.syntax * 'Auu____5532) ->
      FStar_Range.range
  =
  fun uu____5543  ->
    match uu____5543 with | (hd1,uu____5551) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5565 'Auu____5566 .
    ('Auu____5565 FStar_Syntax_Syntax.syntax * 'Auu____5566) Prims.list ->
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
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list -> FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____5664 ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args))
            FStar_Pervasives_Native.None r
  
let (mk_app_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun bs  ->
      let uu____5723 =
        FStar_List.map
          (fun uu____5750  ->
             match uu____5750 with
             | (bv,aq) ->
                 let uu____5769 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5769, aq)) bs
         in
      mk_app f uu____5723
  
let (mk_data :
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Syntax_Syntax.syntax)
  =
  fun l  ->
    fun args  ->
      match args with
      | [] ->
          let uu____5819 = FStar_Ident.range_of_lid l  in
          let uu____5820 =
            let uu____5829 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5829  in
          uu____5820 FStar_Pervasives_Native.None uu____5819
      | uu____5834 ->
          let e =
            let uu____5848 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5848 args  in
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
  
let (field_projector_prefix : Prims.string) = "__proj__" 
let (field_projector_sep : Prims.string) = "__item__" 
let (field_projector_contains_constructor : Prims.string -> Prims.bool) =
  fun s  -> FStar_Util.starts_with s field_projector_prefix 
let (mk_field_projector_name_from_string :
  Prims.string -> Prims.string -> Prims.string) =
  fun constr  ->
    fun field  ->
      Prims.op_Hat field_projector_prefix
        (Prims.op_Hat constr (Prims.op_Hat field_projector_sep field))
  
let (mk_field_projector_name_from_ident :
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun lid  ->
    fun i  ->
      let itext = i.FStar_Ident.idText  in
      let newi =
        if field_projector_contains_constructor itext
        then i
        else
          FStar_Ident.mk_ident
            ((mk_field_projector_name_from_string
                (lid.FStar_Ident.ident).FStar_Ident.idText itext),
              (i.FStar_Ident.idRange))
         in
      FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns [newi])
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv ->
      Prims.int -> (FStar_Ident.lident * FStar_Syntax_Syntax.bv))
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5925 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5925
          then
            let uu____5928 =
              let uu____5934 =
                let uu____5936 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5936  in
              let uu____5939 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5934, uu____5939)  in
            FStar_Ident.mk_ident uu____5928
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___993_5944 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___993_5944.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___993_5944.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5945 = mk_field_projector_name_from_ident lid nm  in
        (uu____5945, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5957) -> ses
    | uu____5966 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____5977 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (map_match_wps :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    (FStar_Syntax_Syntax.match_with_close,FStar_Syntax_Syntax.match_with_subst)
      FStar_Util.either ->
      (FStar_Syntax_Syntax.match_with_close,FStar_Syntax_Syntax.match_with_subst)
        FStar_Util.either)
  =
  fun f  ->
    fun match_wp  ->
      match match_wp with
      | FStar_Util.Inl r ->
          let uu____6012 =
            let uu___1010_6013 = r  in
            let uu____6014 = f r.FStar_Syntax_Syntax.if_then_else  in
            let uu____6015 = f r.FStar_Syntax_Syntax.ite_wp  in
            let uu____6016 = f r.FStar_Syntax_Syntax.close_wp  in
            {
              FStar_Syntax_Syntax.if_then_else = uu____6014;
              FStar_Syntax_Syntax.ite_wp = uu____6015;
              FStar_Syntax_Syntax.close_wp = uu____6016
            }  in
          FStar_Util.Inl uu____6012
      | FStar_Util.Inr r ->
          let uu____6018 =
            let uu___1014_6019 = r  in
            let uu____6020 = f r.FStar_Syntax_Syntax.conjunction  in
            { FStar_Syntax_Syntax.conjunction = uu____6020 }  in
          FStar_Util.Inr uu____6018
  
let (get_match_with_close_wps :
  (FStar_Syntax_Syntax.match_with_close,FStar_Syntax_Syntax.match_with_subst)
    FStar_Util.either ->
    (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme *
      FStar_Syntax_Syntax.tscheme))
  =
  fun match_wp  ->
    match match_wp with
    | FStar_Util.Inl r ->
        ((r.FStar_Syntax_Syntax.if_then_else),
          (r.FStar_Syntax_Syntax.ite_wp), (r.FStar_Syntax_Syntax.close_wp))
    | uu____6048 ->
        failwith
          "Impossible! get_match_with_close_wps called with a match_with_subst wp"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____6071 = FStar_Syntax_Unionfind.find uv  in
      match uu____6071 with
      | FStar_Pervasives_Native.Some uu____6074 ->
          let uu____6075 =
            let uu____6077 =
              let uu____6079 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____6079  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____6077  in
          failwith uu____6075
      | uu____6084 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____6167 -> q1 = q2
  
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
              let uu____6213 =
                let uu___1068_6214 = rc  in
                let uu____6215 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1068_6214.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6215;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1068_6214.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6213
           in
        match bs with
        | [] -> t
        | uu____6232 ->
            let body =
              let uu____6234 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6234  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6264 =
                   let uu____6271 =
                     let uu____6272 =
                       let uu____6291 =
                         let uu____6300 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6300 bs'  in
                       let uu____6315 = close_lopt lopt'  in
                       (uu____6291, t1, uu____6315)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6272  in
                   FStar_Syntax_Syntax.mk uu____6271  in
                 uu____6264 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6330 ->
                 let uu____6331 =
                   let uu____6338 =
                     let uu____6339 =
                       let uu____6358 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6367 = close_lopt lopt  in
                       (uu____6358, body, uu____6367)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6339  in
                   FStar_Syntax_Syntax.mk uu____6338  in
                 uu____6331 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos)
  
let (arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____6423 ->
          let uu____6432 =
            let uu____6439 =
              let uu____6440 =
                let uu____6455 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6464 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6455, uu____6464)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6440  in
            FStar_Syntax_Syntax.mk uu____6439  in
          uu____6432 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6513 =
        let uu____6514 = FStar_Syntax_Subst.compress t  in
        uu____6514.FStar_Syntax_Syntax.n  in
      match uu____6513 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6544) ->
               let uu____6553 =
                 let uu____6554 = FStar_Syntax_Subst.compress tres  in
                 uu____6554.FStar_Syntax_Syntax.n  in
               (match uu____6553 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6597 -> t)
           | uu____6598 -> t)
      | uu____6599 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6617 =
        let uu____6618 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6618 t.FStar_Syntax_Syntax.pos  in
      let uu____6619 =
        let uu____6626 =
          let uu____6627 =
            let uu____6634 =
              let uu____6637 =
                let uu____6638 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6638]  in
              FStar_Syntax_Subst.close uu____6637 t  in
            (b, uu____6634)  in
          FStar_Syntax_Syntax.Tm_refine uu____6627  in
        FStar_Syntax_Syntax.mk uu____6626  in
      uu____6619 FStar_Pervasives_Native.None uu____6617
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____6718 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6718 with
         | (bs1,c1) ->
             let uu____6737 = is_total_comp c1  in
             if uu____6737
             then
               let uu____6752 = arrow_formals_comp (comp_result c1)  in
               (match uu____6752 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6819;
           FStar_Syntax_Syntax.index = uu____6820;
           FStar_Syntax_Syntax.sort = s;_},uu____6822)
        ->
        let rec aux s1 k2 =
          let uu____6853 =
            let uu____6854 = FStar_Syntax_Subst.compress s1  in
            uu____6854.FStar_Syntax_Syntax.n  in
          match uu____6853 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6869 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6884;
                 FStar_Syntax_Syntax.index = uu____6885;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6887)
              -> aux s2 k2
          | uu____6895 ->
              let uu____6896 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6896)
           in
        aux s k1
    | uu____6911 ->
        let uu____6912 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6912)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6947 = arrow_formals_comp k  in
    match uu____6947 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7089 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7089 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____7113 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___12_7122  ->
                         match uu___12_7122 with
                         | FStar_Syntax_Syntax.DECREASES uu____7124 -> true
                         | uu____7128 -> false))
                  in
               (match uu____7113 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7163 ->
                    let uu____7166 = is_total_comp c1  in
                    if uu____7166
                    then
                      let uu____7185 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7185 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7278;
             FStar_Syntax_Syntax.index = uu____7279;
             FStar_Syntax_Syntax.sort = k2;_},uu____7281)
          -> arrow_until_decreases k2
      | uu____7289 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7310 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7310 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7364 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7385 =
                 FStar_Common.tabulate n_univs (fun uu____7391  -> false)  in
               let uu____7394 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7419  ->
                         match uu____7419 with
                         | (x,uu____7428) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7385 uu____7394)
           in
        ((n_univs + (FStar_List.length bs)), uu____7364)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7484 =
            let uu___1190_7485 = rc  in
            let uu____7486 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1190_7485.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7486;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1190_7485.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7484
      | uu____7495 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7529 =
        let uu____7530 =
          let uu____7533 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7533  in
        uu____7530.FStar_Syntax_Syntax.n  in
      match uu____7529 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7579 = aux t2 what  in
          (match uu____7579 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7651 -> ([], t1, abs_body_lcomp)  in
    let uu____7668 = aux t FStar_Pervasives_Native.None  in
    match uu____7668 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7716 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7716 with
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
                    | (FStar_Pervasives_Native.None ,uu____7879) -> def
                    | (uu____7890,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7902) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _7918  ->
                                  FStar_Syntax_Syntax.U_name _7918))
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
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____8000 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____8000 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____8035 ->
            let t' = arrow binders c  in
            let uu____8047 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____8047 with
             | (uvs1,t'1) ->
                 let uu____8068 =
                   let uu____8069 = FStar_Syntax_Subst.compress t'1  in
                   uu____8069.FStar_Syntax_Syntax.n  in
                 (match uu____8068 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8118 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____8143 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8154 -> false
  
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
      let uu____8217 =
        let uu____8218 = pre_typ t  in uu____8218.FStar_Syntax_Syntax.n  in
      match uu____8217 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8223 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8237 =
        let uu____8238 = pre_typ t  in uu____8238.FStar_Syntax_Syntax.n  in
      match uu____8237 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8242 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8244) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8270) ->
          is_constructed_typ t1 lid
      | uu____8275 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8288 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8289 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8290 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8292) -> get_tycon t2
    | uu____8317 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8325 =
      let uu____8326 = un_uinst t  in uu____8326.FStar_Syntax_Syntax.n  in
    match uu____8325 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8331 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8345 =
        let uu____8349 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8349  in
      match uu____8345 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8381 -> false
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
  unit -> (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe)) =
  fun uu____8400  ->
    let u =
      let uu____8406 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _8423  -> FStar_Syntax_Syntax.U_unif _8423)
        uu____8406
       in
    let uu____8424 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8424, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8437 = eq_tm a a'  in
      match uu____8437 with | Equal  -> true | uu____8440 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8445 =
    let uu____8452 =
      let uu____8453 =
        let uu____8454 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8454
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8453  in
    FStar_Syntax_Syntax.mk uu____8452  in
  uu____8445 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
    FStar_Pervasives_Native.None
  
let (tiff : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (2)))
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
let (tcdecltime_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.tcdecltime_attr 
let (inline_let_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.inline_let_attr 
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
          let uu____8566 =
            let uu____8569 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8570 =
              let uu____8577 =
                let uu____8578 =
                  let uu____8595 =
                    let uu____8606 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8615 =
                      let uu____8626 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8626]  in
                    uu____8606 :: uu____8615  in
                  (tand, uu____8595)  in
                FStar_Syntax_Syntax.Tm_app uu____8578  in
              FStar_Syntax_Syntax.mk uu____8577  in
            uu____8570 FStar_Pervasives_Native.None uu____8569  in
          FStar_Pervasives_Native.Some uu____8566
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8703 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8704 =
          let uu____8711 =
            let uu____8712 =
              let uu____8729 =
                let uu____8740 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8749 =
                  let uu____8760 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8760]  in
                uu____8740 :: uu____8749  in
              (op_t, uu____8729)  in
            FStar_Syntax_Syntax.Tm_app uu____8712  in
          FStar_Syntax_Syntax.mk uu____8711  in
        uu____8704 FStar_Pervasives_Native.None uu____8703
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8817 =
      let uu____8824 =
        let uu____8825 =
          let uu____8842 =
            let uu____8853 = FStar_Syntax_Syntax.as_arg phi  in [uu____8853]
             in
          (t_not, uu____8842)  in
        FStar_Syntax_Syntax.Tm_app uu____8825  in
      FStar_Syntax_Syntax.mk uu____8824  in
    uu____8817 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____9050 =
      let uu____9057 =
        let uu____9058 =
          let uu____9075 =
            let uu____9086 = FStar_Syntax_Syntax.as_arg e  in [uu____9086]
             in
          (b2t_v, uu____9075)  in
        FStar_Syntax_Syntax.Tm_app uu____9058  in
      FStar_Syntax_Syntax.mk uu____9057  in
    uu____9050 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9133 = head_and_args e  in
    match uu____9133 with
    | (hd1,args) ->
        let uu____9178 =
          let uu____9193 =
            let uu____9194 = FStar_Syntax_Subst.compress hd1  in
            uu____9194.FStar_Syntax_Syntax.n  in
          (uu____9193, args)  in
        (match uu____9178 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9211)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9246 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9268 =
      let uu____9269 = unmeta t  in uu____9269.FStar_Syntax_Syntax.n  in
    match uu____9268 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9274 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9297 = is_t_true t1  in
      if uu____9297
      then t2
      else
        (let uu____9304 = is_t_true t2  in
         if uu____9304 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9332 = is_t_true t1  in
      if uu____9332
      then t_true
      else
        (let uu____9339 = is_t_true t2  in
         if uu____9339 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9368 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9369 =
        let uu____9376 =
          let uu____9377 =
            let uu____9394 =
              let uu____9405 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9414 =
                let uu____9425 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9425]  in
              uu____9405 :: uu____9414  in
            (teq, uu____9394)  in
          FStar_Syntax_Syntax.Tm_app uu____9377  in
        FStar_Syntax_Syntax.mk uu____9376  in
      uu____9369 FStar_Pervasives_Native.None uu____9368
  
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
          let uu____9492 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9493 =
            let uu____9500 =
              let uu____9501 =
                let uu____9518 =
                  let uu____9529 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9538 =
                    let uu____9549 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9558 =
                      let uu____9569 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9569]  in
                    uu____9549 :: uu____9558  in
                  uu____9529 :: uu____9538  in
                (eq_inst, uu____9518)  in
              FStar_Syntax_Syntax.Tm_app uu____9501  in
            FStar_Syntax_Syntax.mk uu____9500  in
          uu____9493 FStar_Pervasives_Native.None uu____9492
  
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
        let uu____9646 =
          let uu____9653 =
            let uu____9654 =
              let uu____9671 =
                let uu____9682 = FStar_Syntax_Syntax.iarg t  in
                let uu____9691 =
                  let uu____9702 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9711 =
                    let uu____9722 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9722]  in
                  uu____9702 :: uu____9711  in
                uu____9682 :: uu____9691  in
              (t_has_type1, uu____9671)  in
            FStar_Syntax_Syntax.Tm_app uu____9654  in
          FStar_Syntax_Syntax.mk uu____9653  in
        uu____9646 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9799 =
          let uu____9806 =
            let uu____9807 =
              let uu____9824 =
                let uu____9835 = FStar_Syntax_Syntax.iarg t  in
                let uu____9844 =
                  let uu____9855 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9855]  in
                uu____9835 :: uu____9844  in
              (t_with_type1, uu____9824)  in
            FStar_Syntax_Syntax.Tm_app uu____9807  in
          FStar_Syntax_Syntax.mk uu____9806  in
        uu____9799 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9902 =
    let uu____9909 =
      let uu____9910 =
        let uu____9917 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9917, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9910  in
    FStar_Syntax_Syntax.mk uu____9909  in
  uu____9902 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (lex_pair : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (tforall : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
    FStar_Pervasives_Native.None
  
let (t_haseq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
  
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.lcomp) =
  fun c0  ->
    let uu____9932 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____9945 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____9956 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____9932 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____9977  -> c0)
  
let (mk_residual_comp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.cflag Prims.list ->
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
        let uu____10060 =
          let uu____10067 =
            let uu____10068 =
              let uu____10085 =
                let uu____10096 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____10105 =
                  let uu____10116 =
                    let uu____10125 =
                      let uu____10126 =
                        let uu____10127 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10127]  in
                      abs uu____10126 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10125  in
                  [uu____10116]  in
                uu____10096 :: uu____10105  in
              (fa, uu____10085)  in
            FStar_Syntax_Syntax.Tm_app uu____10068  in
          FStar_Syntax_Syntax.mk uu____10067  in
        uu____10060 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____10254 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10254
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10273 -> true
    | uu____10275 -> false
  
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
          let uu____10322 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10322, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10351 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10351, FStar_Pervasives_Native.None, t2)  in
        let uu____10365 =
          let uu____10366 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10366  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10365
  
let (mk_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          FStar_Pervasives_Native.None
         in
      let uu____10442 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10445 =
        let uu____10456 = FStar_Syntax_Syntax.as_arg p  in [uu____10456]  in
      mk_app uu____10442 uu____10445
  
let (mk_auto_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (2)))
          FStar_Pervasives_Native.None
         in
      let uu____10496 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10499 =
        let uu____10510 = FStar_Syntax_Syntax.as_arg p  in [uu____10510]  in
      mk_app uu____10496 uu____10499
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10545 = head_and_args t  in
    match uu____10545 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____10594 =
          let uu____10609 =
            let uu____10610 = FStar_Syntax_Subst.compress head3  in
            uu____10610.FStar_Syntax_Syntax.n  in
          (uu____10609, args)  in
        (match uu____10594 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10629)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10695 =
                    let uu____10700 =
                      let uu____10701 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10701]  in
                    FStar_Syntax_Subst.open_term uu____10700 p  in
                  (match uu____10695 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10758 -> failwith "impossible"  in
                       let uu____10766 =
                         let uu____10768 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10768
                          in
                       if uu____10766
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10784 -> FStar_Pervasives_Native.None)
         | uu____10787 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10818 = head_and_args t  in
    match uu____10818 with
    | (head1,args) ->
        let uu____10869 =
          let uu____10884 =
            let uu____10885 = FStar_Syntax_Subst.compress head1  in
            uu____10885.FStar_Syntax_Syntax.n  in
          (uu____10884, args)  in
        (match uu____10869 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10907;
               FStar_Syntax_Syntax.vars = uu____10908;_},u::[]),(t1,uu____10911)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10958 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10993 = head_and_args t  in
    match uu____10993 with
    | (head1,args) ->
        let uu____11044 =
          let uu____11059 =
            let uu____11060 = FStar_Syntax_Subst.compress head1  in
            uu____11060.FStar_Syntax_Syntax.n  in
          (uu____11059, args)  in
        (match uu____11044 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____11082;
               FStar_Syntax_Syntax.vars = uu____11083;_},u::[]),(t1,uu____11086)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11133 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11161 =
      let uu____11178 = unmeta t  in head_and_args uu____11178  in
    match uu____11161 with
    | (head1,uu____11181) ->
        let uu____11206 =
          let uu____11207 = un_uinst head1  in
          uu____11207.FStar_Syntax_Syntax.n  in
        (match uu____11206 with
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
         | uu____11212 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11232 =
      let uu____11245 =
        let uu____11246 = FStar_Syntax_Subst.compress t  in
        uu____11246.FStar_Syntax_Syntax.n  in
      match uu____11245 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____11376 =
            let uu____11387 =
              let uu____11388 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____11388  in
            (b, uu____11387)  in
          FStar_Pervasives_Native.Some uu____11376
      | uu____11405 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____11232
      (fun uu____11443  ->
         match uu____11443 with
         | (b,c) ->
             let uu____11480 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11480 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11543 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11580 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11580
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11632 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11675 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11716 -> false
  
let (__proj__BaseConn__item___0 :
  connective -> (FStar_Ident.lident * FStar_Syntax_Syntax.args)) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0 
let (destruct_base_table :
  (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list)
    Prims.list)
  =
  let f x = (x, x)  in
  [(Prims.int_zero,
     [f FStar_Parser_Const.true_lid; f FStar_Parser_Const.false_lid]);
  ((Prims.of_int (2)),
    [f FStar_Parser_Const.and_lid;
    f FStar_Parser_Const.or_lid;
    f FStar_Parser_Const.imp_lid;
    f FStar_Parser_Const.iff_lid;
    f FStar_Parser_Const.eq2_lid;
    f FStar_Parser_Const.eq3_lid]);
  (Prims.int_one, [f FStar_Parser_Const.not_lid]);
  ((Prims.of_int (3)),
    [f FStar_Parser_Const.ite_lid; f FStar_Parser_Const.eq2_lid]);
  ((Prims.of_int (4)), [f FStar_Parser_Const.eq3_lid])] 
let (destruct_sq_base_table :
  (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list)
    Prims.list)
  =
  [((Prims.of_int (2)),
     [(FStar_Parser_Const.c_and_lid, FStar_Parser_Const.and_lid);
     (FStar_Parser_Const.c_or_lid, FStar_Parser_Const.or_lid);
     (FStar_Parser_Const.c_eq2_lid, FStar_Parser_Const.c_eq2_lid);
     (FStar_Parser_Const.c_eq3_lid, FStar_Parser_Const.c_eq3_lid)]);
  ((Prims.of_int (3)),
    [(FStar_Parser_Const.c_eq2_lid, FStar_Parser_Const.c_eq2_lid)]);
  ((Prims.of_int (4)),
    [(FStar_Parser_Const.c_eq3_lid, FStar_Parser_Const.c_eq3_lid)]);
  (Prims.int_zero,
    [(FStar_Parser_Const.c_true_lid, FStar_Parser_Const.true_lid);
    (FStar_Parser_Const.c_false_lid, FStar_Parser_Const.false_lid)])]
  
let (destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1  in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____12102) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____12114) ->
          unmeta_monadic t
      | uu____12127 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12196 =
        match uu____12196 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12234  ->
                   match uu____12234 with
                   | (lid,out_lid) ->
                       let uu____12243 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12243
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12270 = head_and_args t  in
      match uu____12270 with
      | (hd1,args) ->
          let uu____12315 =
            let uu____12316 = un_uinst hd1  in
            uu____12316.FStar_Syntax_Syntax.n  in
          (match uu____12315 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12322 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12331 = un_squash t  in
      FStar_Util.bind_opt uu____12331
        (fun t1  ->
           let uu____12347 = head_and_args' t1  in
           match uu____12347 with
           | (hd1,args) ->
               let uu____12386 =
                 let uu____12387 = un_uinst hd1  in
                 uu____12387.FStar_Syntax_Syntax.n  in
               (match uu____12386 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12393 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12434,pats)) ->
          let uu____12472 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12472)
      | uu____12485 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12552 = head_and_args t1  in
        match uu____12552 with
        | (t2,args) ->
            let uu____12607 = un_uinst t2  in
            let uu____12608 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12649  ->
                      match uu____12649 with
                      | (t3,imp) ->
                          let uu____12668 = unascribe t3  in
                          (uu____12668, imp)))
               in
            (uu____12607, uu____12608)
         in
      let rec aux qopt out t1 =
        let uu____12719 = let uu____12743 = flat t1  in (qopt, uu____12743)
           in
        match uu____12719 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12783;
                 FStar_Syntax_Syntax.vars = uu____12784;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12787);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12788;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12789;_},uu____12790)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12892;
                 FStar_Syntax_Syntax.vars = uu____12893;_},uu____12894::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12897);
                  FStar_Syntax_Syntax.pos = uu____12898;
                  FStar_Syntax_Syntax.vars = uu____12899;_},uu____12900)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13017;
               FStar_Syntax_Syntax.vars = uu____13018;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____13021);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____13022;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____13023;_},uu____13024)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13117 =
              let uu____13121 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13121  in
            aux uu____13117 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13131;
               FStar_Syntax_Syntax.vars = uu____13132;_},uu____13133::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____13136);
                FStar_Syntax_Syntax.pos = uu____13137;
                FStar_Syntax_Syntax.vars = uu____13138;_},uu____13139)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13248 =
              let uu____13252 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13252  in
            aux uu____13248 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13262) ->
            let bs = FStar_List.rev out  in
            let uu____13315 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13315 with
             | (bs1,t2) ->
                 let uu____13324 = patterns t2  in
                 (match uu____13324 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13374 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13429 = un_squash t  in
      FStar_Util.bind_opt uu____13429
        (fun t1  ->
           let uu____13444 = arrow_one t1  in
           match uu____13444 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13459 =
                 let uu____13461 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13461  in
               if uu____13459
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13471 = comp_to_comp_typ_nouniv c  in
                    uu____13471.FStar_Syntax_Syntax.result_typ  in
                  let uu____13472 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13472
                  then
                    let uu____13479 = patterns q  in
                    match uu____13479 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13542 =
                       let uu____13543 =
                         let uu____13548 =
                           let uu____13549 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13560 =
                             let uu____13571 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13571]  in
                           uu____13549 :: uu____13560  in
                         (FStar_Parser_Const.imp_lid, uu____13548)  in
                       BaseConn uu____13543  in
                     FStar_Pervasives_Native.Some uu____13542))
           | uu____13604 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13612 = un_squash t  in
      FStar_Util.bind_opt uu____13612
        (fun t1  ->
           let uu____13643 = head_and_args' t1  in
           match uu____13643 with
           | (hd1,args) ->
               let uu____13682 =
                 let uu____13697 =
                   let uu____13698 = un_uinst hd1  in
                   uu____13698.FStar_Syntax_Syntax.n  in
                 (uu____13697, args)  in
               (match uu____13682 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13715)::(a2,uu____13717)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13768 =
                      let uu____13769 = FStar_Syntax_Subst.compress a2  in
                      uu____13769.FStar_Syntax_Syntax.n  in
                    (match uu____13768 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13776) ->
                         let uu____13811 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13811 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13864 -> failwith "impossible"  in
                              let uu____13872 = patterns q1  in
                              (match uu____13872 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13933 -> FStar_Pervasives_Native.None)
                | uu____13934 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13957 = destruct_sq_forall phi  in
          (match uu____13957 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13967  -> FStar_Pervasives_Native.Some _13967)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13974 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13980 = destruct_sq_exists phi  in
          (match uu____13980 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13990  -> FStar_Pervasives_Native.Some _13990)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13997 -> f1)
      | uu____14000 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____14004 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____14004
      (fun uu____14009  ->
         let uu____14010 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____14010
           (fun uu____14015  ->
              let uu____14016 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____14016
                (fun uu____14021  ->
                   let uu____14022 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____14022
                     (fun uu____14027  ->
                        let uu____14028 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____14028
                          (fun uu____14032  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____14050 =
            let uu____14055 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____14055  in
          let uu____14056 =
            let uu____14057 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____14057  in
          let uu____14060 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____14050 a.FStar_Syntax_Syntax.action_univs uu____14056
            FStar_Parser_Const.effect_Tot_lid uu____14060 [] pos
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
    let reify_1 =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
       in
    let uu____14086 =
      let uu____14093 =
        let uu____14094 =
          let uu____14111 =
            let uu____14122 = FStar_Syntax_Syntax.as_arg t  in [uu____14122]
             in
          (reify_1, uu____14111)  in
        FStar_Syntax_Syntax.Tm_app uu____14094  in
      FStar_Syntax_Syntax.mk uu____14093  in
    uu____14086 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14174 =
        let uu____14181 =
          let uu____14182 =
            let uu____14183 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14183  in
          FStar_Syntax_Syntax.Tm_constant uu____14182  in
        FStar_Syntax_Syntax.mk uu____14181  in
      uu____14174 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14185 =
      let uu____14192 =
        let uu____14193 =
          let uu____14210 =
            let uu____14221 = FStar_Syntax_Syntax.as_arg t  in [uu____14221]
             in
          (reflect_, uu____14210)  in
        FStar_Syntax_Syntax.Tm_app uu____14193  in
      FStar_Syntax_Syntax.mk uu____14192  in
    uu____14185 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14265 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14290 = unfold_lazy i  in delta_qualifier uu____14290
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14292 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14293 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14294 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14317 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14330 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14331 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14338 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14339 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14355) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14360;
           FStar_Syntax_Syntax.index = uu____14361;
           FStar_Syntax_Syntax.sort = t2;_},uu____14363)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14372) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14378,uu____14379) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14421) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14446,t2,uu____14448) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14473,t2) -> delta_qualifier t2
  
let rec (incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth) =
  fun d  ->
    match d with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Syntax_Syntax.Delta_constant_at_level (i + Prims.int_one)
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Syntax_Syntax.Delta_equational_at_level (i + Prims.int_one)
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
  
let (incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let uu____14512 = delta_qualifier t  in incr_delta_depth uu____14512
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14520 =
      let uu____14521 = FStar_Syntax_Subst.compress t  in
      uu____14521.FStar_Syntax_Syntax.n  in
    match uu____14520 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14526 -> false
  
let rec apply_last :
  'Auu____14535 .
    ('Auu____14535 -> 'Auu____14535) ->
      'Auu____14535 Prims.list -> 'Auu____14535 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14561 = f a  in [uu____14561]
      | x::xs -> let uu____14566 = apply_last f xs  in x :: uu____14566
  
let (dm4f_lid :
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident) =
  fun ed  ->
    fun name  ->
      let p = FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname  in
      let p' =
        apply_last
          (fun s  ->
             Prims.op_Hat "_dm4f_" (Prims.op_Hat s (Prims.op_Hat "_" name)))
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
          let uu____14621 =
            let uu____14628 =
              let uu____14629 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14629  in
            FStar_Syntax_Syntax.mk uu____14628  in
          uu____14621 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____14643 =
            let uu____14648 =
              let uu____14649 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14649
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14648 args  in
          uu____14643 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14663 =
            let uu____14668 =
              let uu____14669 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14669
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14668 args  in
          uu____14663 FStar_Pervasives_Native.None pos  in
        let uu____14670 =
          let uu____14671 =
            let uu____14672 = FStar_Syntax_Syntax.iarg typ  in [uu____14672]
             in
          nil uu____14671 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14706 =
                 let uu____14707 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14716 =
                   let uu____14727 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14736 =
                     let uu____14747 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14747]  in
                   uu____14727 :: uu____14736  in
                 uu____14707 :: uu____14716  in
               cons1 uu____14706 t.FStar_Syntax_Syntax.pos) l uu____14670
  
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
        | uu____14856 -> false
  
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
          | uu____14970 -> false
  
let eqprod :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) -> ('a * 'b) -> ('a * 'b) -> Prims.bool
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
        | uu____15136 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15174 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15174
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
        let t11 = let uu____15396 = unmeta_safe t1  in canon_app uu____15396
           in
        let t21 = let uu____15402 = unmeta_safe t2  in canon_app uu____15402
           in
        let uu____15405 =
          let uu____15410 =
            let uu____15411 =
              let uu____15414 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15414  in
            uu____15411.FStar_Syntax_Syntax.n  in
          let uu____15415 =
            let uu____15416 =
              let uu____15419 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15419  in
            uu____15416.FStar_Syntax_Syntax.n  in
          (uu____15410, uu____15415)  in
        match uu____15405 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15421,uu____15422) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15431,FStar_Syntax_Syntax.Tm_uinst uu____15432) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15441,uu____15442) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15467,FStar_Syntax_Syntax.Tm_delayed uu____15468) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15493,uu____15494) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15523,FStar_Syntax_Syntax.Tm_ascribed uu____15524) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15563 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15563
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15568 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15568
        | (FStar_Syntax_Syntax.Tm_type
           uu____15571,FStar_Syntax_Syntax.Tm_type uu____15572) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15630 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15630) &&
              (let uu____15640 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15640)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15689 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15689) &&
              (let uu____15699 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15699)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15716 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15716) &&
              (let uu____15720 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15720)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15777 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15777) &&
              (let uu____15781 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15781)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15870 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15870) &&
              (let uu____15874 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15874)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15891,uu____15892) ->
            let uu____15893 =
              let uu____15895 = unlazy t11  in
              term_eq_dbg dbg uu____15895 t21  in
            check "lazy_l" uu____15893
        | (uu____15897,FStar_Syntax_Syntax.Tm_lazy uu____15898) ->
            let uu____15899 =
              let uu____15901 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15901  in
            check "lazy_r" uu____15899
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15946 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15946))
              &&
              (let uu____15950 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15950)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15954),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15956)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____16014 =
               let uu____16016 = eq_quoteinfo qi1 qi2  in uu____16016 = Equal
                in
             check "tm_quoted qi" uu____16014) &&
              (let uu____16019 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____16019)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____16049 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____16049) &&
                   (let uu____16053 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____16053)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____16072 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____16072) &&
                    (let uu____16076 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____16076))
                   &&
                   (let uu____16080 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____16080)
             | uu____16083 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____16089) -> fail "unk"
        | (uu____16091,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____16093,uu____16094) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____16096,uu____16097) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____16099,uu____16100) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____16102,uu____16103) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____16105,uu____16106) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____16108,uu____16109) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____16129,uu____16130) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____16146,uu____16147) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____16155,uu____16156) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____16174,uu____16175) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16199,uu____16200) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16215,uu____16216) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16230,uu____16231) ->
            fail "bottom"
        | (uu____16239,FStar_Syntax_Syntax.Tm_bvar uu____16240) ->
            fail "bottom"
        | (uu____16242,FStar_Syntax_Syntax.Tm_name uu____16243) ->
            fail "bottom"
        | (uu____16245,FStar_Syntax_Syntax.Tm_fvar uu____16246) ->
            fail "bottom"
        | (uu____16248,FStar_Syntax_Syntax.Tm_constant uu____16249) ->
            fail "bottom"
        | (uu____16251,FStar_Syntax_Syntax.Tm_type uu____16252) ->
            fail "bottom"
        | (uu____16254,FStar_Syntax_Syntax.Tm_abs uu____16255) ->
            fail "bottom"
        | (uu____16275,FStar_Syntax_Syntax.Tm_arrow uu____16276) ->
            fail "bottom"
        | (uu____16292,FStar_Syntax_Syntax.Tm_refine uu____16293) ->
            fail "bottom"
        | (uu____16301,FStar_Syntax_Syntax.Tm_app uu____16302) ->
            fail "bottom"
        | (uu____16320,FStar_Syntax_Syntax.Tm_match uu____16321) ->
            fail "bottom"
        | (uu____16345,FStar_Syntax_Syntax.Tm_let uu____16346) ->
            fail "bottom"
        | (uu____16361,FStar_Syntax_Syntax.Tm_uvar uu____16362) ->
            fail "bottom"
        | (uu____16376,FStar_Syntax_Syntax.Tm_meta uu____16377) ->
            fail "bottom"

and (arg_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
        Prims.bool)
  =
  fun dbg  ->
    fun a1  ->
      fun a2  ->
        eqprod
          (fun t1  ->
             fun t2  ->
               let uu____16412 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16412)
          (fun q1  ->
             fun q2  ->
               let uu____16424 =
                 let uu____16426 = eq_aqual q1 q2  in uu____16426 = Equal  in
               check "arg qual" uu____16424) a1 a2

and (binder_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) -> Prims.bool)
  =
  fun dbg  ->
    fun b1  ->
      fun b2  ->
        eqprod
          (fun b11  ->
             fun b21  ->
               let uu____16451 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16451)
          (fun q1  ->
             fun q2  ->
               let uu____16463 =
                 let uu____16465 = eq_aqual q1 q2  in uu____16465 = Equal  in
               check "binder qual" uu____16463) b1 b2

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
        ((let uu____16485 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16485) &&
           (let uu____16489 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16489))
          && true

and (eq_flags_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.cflag -> FStar_Syntax_Syntax.cflag -> Prims.bool)
  = fun dbg  -> fun f1  -> fun f2  -> true

and (branch_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax) -> Prims.bool)
  =
  fun dbg  ->
    fun uu____16499  ->
      fun uu____16500  ->
        match (uu____16499, uu____16500) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16627 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16627) &&
               (let uu____16631 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16631))
              &&
              (let uu____16635 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16677 -> false  in
               check "branch when" uu____16635)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16698 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16698) &&
           (let uu____16707 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16707))
          &&
          (let uu____16711 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16711)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16728 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16728 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16782 ->
        let uu____16805 =
          let uu____16807 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16807  in
        Prims.int_one + uu____16805
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16810 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16810
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16814 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16814
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16823 = sizeof t1  in (FStar_List.length us) + uu____16823
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16827) ->
        let uu____16852 = sizeof t1  in
        let uu____16854 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16869  ->
                 match uu____16869 with
                 | (bv,uu____16879) ->
                     let uu____16884 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16884) Prims.int_zero bs
           in
        uu____16852 + uu____16854
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____16913 = sizeof hd1  in
        let uu____16915 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16930  ->
                 match uu____16930 with
                 | (arg,uu____16940) ->
                     let uu____16945 = sizeof arg  in acc + uu____16945)
            Prims.int_zero args
           in
        uu____16913 + uu____16915
    | uu____16948 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16962 =
        let uu____16963 = un_uinst t  in uu____16963.FStar_Syntax_Syntax.n
         in
      match uu____16962 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16968 -> false
  
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
      let set_options1 s =
        let uu____17012 = FStar_Options.set_options s  in
        match uu____17012 with
        | FStar_Getopt.Success  -> ()
        | FStar_Getopt.Help  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                "Failed to process pragma: use 'fstar --help' to see which options are available")
              r
        | FStar_Getopt.Error s1 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                (Prims.op_Hat "Failed to process pragma: " s1)) r
         in
      match p with
      | FStar_Syntax_Syntax.LightOff  -> FStar_Options.set_ml_ish ()
      | FStar_Syntax_Syntax.SetOptions o -> set_options1 o
      | FStar_Syntax_Syntax.ResetOptions sopt ->
          ((let uu____17026 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____17026 (fun a1  -> ()));
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s -> set_options1 s))
      | FStar_Syntax_Syntax.PushOptions sopt ->
          (FStar_Options.internal_push ();
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s -> set_options1 s))
      | FStar_Syntax_Syntax.RestartSolver  -> ()
      | FStar_Syntax_Syntax.PopOptions  ->
          let uu____17041 = FStar_Options.internal_pop ()  in
          if uu____17041
          then ()
          else
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                "Cannot #pop-options, stack would become empty") r
  
let rec (unbound_variables :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun tm  ->
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____17073 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17100 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17115 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17116 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17117 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17126) ->
        let uu____17151 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17151 with
         | (bs1,t2) ->
             let uu____17160 =
               FStar_List.collect
                 (fun uu____17172  ->
                    match uu____17172 with
                    | (b,uu____17182) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17187 = unbound_variables t2  in
             FStar_List.append uu____17160 uu____17187)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17212 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17212 with
         | (bs1,c1) ->
             let uu____17221 =
               FStar_List.collect
                 (fun uu____17233  ->
                    match uu____17233 with
                    | (b,uu____17243) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17248 = unbound_variables_comp c1  in
             FStar_List.append uu____17221 uu____17248)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17257 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17257 with
         | (bs,t2) ->
             let uu____17280 =
               FStar_List.collect
                 (fun uu____17292  ->
                    match uu____17292 with
                    | (b1,uu____17302) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17307 = unbound_variables t2  in
             FStar_List.append uu____17280 uu____17307)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17336 =
          FStar_List.collect
            (fun uu____17350  ->
               match uu____17350 with
               | (x,uu____17362) -> unbound_variables x) args
           in
        let uu____17371 = unbound_variables t1  in
        FStar_List.append uu____17336 uu____17371
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17412 = unbound_variables t1  in
        let uu____17415 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17430 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17430 with
                  | (p,wopt,t2) ->
                      let uu____17452 = unbound_variables t2  in
                      let uu____17455 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17452 uu____17455))
           in
        FStar_List.append uu____17412 uu____17415
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17469) ->
        let uu____17510 = unbound_variables t1  in
        let uu____17513 =
          let uu____17516 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17547 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17516 uu____17547  in
        FStar_List.append uu____17510 uu____17513
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17588 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17591 =
          let uu____17594 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17597 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17602 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17604 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17604 with
                 | (uu____17625,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17594 uu____17597  in
        FStar_List.append uu____17588 uu____17591
    | FStar_Syntax_Syntax.Tm_let ((uu____17627,lbs),t1) ->
        let uu____17647 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17647 with
         | (lbs1,t2) ->
             let uu____17662 = unbound_variables t2  in
             let uu____17665 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17672 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17675 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17672 uu____17675) lbs1
                in
             FStar_List.append uu____17662 uu____17665)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17692 = unbound_variables t1  in
        let uu____17695 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17700,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17755  ->
                      match uu____17755 with
                      | (a,uu____17767) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17776,uu____17777,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17783,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17789 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17798 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17799 -> []  in
        FStar_List.append uu____17692 uu____17695

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17806) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17816) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17826 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17829 =
          FStar_List.collect
            (fun uu____17843  ->
               match uu____17843 with
               | (a,uu____17855) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17826 uu____17829

let (extract_attr' :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.term Prims.list ->
      (FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid  ->
    fun attrs  ->
      let rec aux acc attrs1 =
        match attrs1 with
        | [] -> FStar_Pervasives_Native.None
        | h::t ->
            let uu____17970 = head_and_args h  in
            (match uu____17970 with
             | (head1,args) ->
                 let uu____18031 =
                   let uu____18032 = FStar_Syntax_Subst.compress head1  in
                   uu____18032.FStar_Syntax_Syntax.n  in
                 (match uu____18031 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18085 -> aux (h :: acc) t))
         in
      aux [] attrs
  
let (extract_attr :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid  ->
    fun se  ->
      let uu____18109 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18109 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2533_18151 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2533_18151.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2533_18151.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2533_18151.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2533_18151.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18159 =
      let uu____18160 = FStar_Syntax_Subst.compress t  in
      uu____18160.FStar_Syntax_Syntax.n  in
    match uu____18159 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18164,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18192)::uu____18193 ->
                  let pats' = unmeta pats  in
                  let uu____18253 = head_and_args pats'  in
                  (match uu____18253 with
                   | (head1,uu____18272) ->
                       let uu____18297 =
                         let uu____18298 = un_uinst head1  in
                         uu____18298.FStar_Syntax_Syntax.n  in
                       (match uu____18297 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18303 -> false))
              | uu____18305 -> false)
         | uu____18317 -> false)
    | uu____18319 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18335 =
      let uu____18352 = unmeta e  in head_and_args uu____18352  in
    match uu____18335 with
    | (head1,args) ->
        let uu____18383 =
          let uu____18398 =
            let uu____18399 = un_uinst head1  in
            uu____18399.FStar_Syntax_Syntax.n  in
          (uu____18398, args)  in
        (match uu____18383 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18417) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18441::(hd1,uu____18443)::(tl1,uu____18445)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18512 =
               let uu____18515 =
                 let uu____18518 = list_elements tl1  in
                 FStar_Util.must uu____18518  in
               hd1 :: uu____18515  in
             FStar_Pervasives_Native.Some uu____18512
         | uu____18527 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18556 =
      let uu____18557 = FStar_Syntax_Subst.compress t  in
      uu____18557.FStar_Syntax_Syntax.n  in
    match uu____18556 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18564) ->
        let uu____18599 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18599 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18633 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18633
             then
               let uu____18640 =
                 let uu____18651 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18651]  in
               mk_app t uu____18640
             else e1)
    | uu____18678 ->
        let uu____18679 =
          let uu____18690 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18690]  in
        mk_app t uu____18679
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18745 = list_elements e  in
        match uu____18745 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18776 =
          let uu____18793 = unmeta p  in
          FStar_All.pipe_right uu____18793 head_and_args  in
        match uu____18776 with
        | (head1,args) ->
            let uu____18844 =
              let uu____18859 =
                let uu____18860 = un_uinst head1  in
                uu____18860.FStar_Syntax_Syntax.n  in
              (uu____18859, args)  in
            (match uu____18844 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18882,uu____18883)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18935 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____18990 =
            let uu____19007 = unmeta t1  in
            FStar_All.pipe_right uu____19007 head_and_args  in
          match uu____18990 with
          | (head1,args) ->
              let uu____19054 =
                let uu____19069 =
                  let uu____19070 = un_uinst head1  in
                  uu____19070.FStar_Syntax_Syntax.n  in
                (uu____19069, args)  in
              (match uu____19054 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19089)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19126 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19156 = smt_pat_or1 t1  in
            (match uu____19156 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19178 = list_elements1 e  in
                 FStar_All.pipe_right uu____19178
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19208 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19208
                           (FStar_List.map one_pat)))
             | uu____19231 ->
                 let uu____19236 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19236])
        | uu____19287 ->
            let uu____19290 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19290]
         in
      let uu____19341 =
        let uu____19374 =
          let uu____19375 = FStar_Syntax_Subst.compress t  in
          uu____19375.FStar_Syntax_Syntax.n  in
        match uu____19374 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19432 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19432 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19503;
                        FStar_Syntax_Syntax.effect_name = uu____19504;
                        FStar_Syntax_Syntax.result_typ = uu____19505;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19507)::(post,uu____19509)::(pats,uu____19511)::[];
                        FStar_Syntax_Syntax.flags = uu____19512;_}
                      ->
                      let uu____19573 = lemma_pats pats  in
                      (binders1, pre, post, uu____19573)
                  | uu____19610 -> failwith "impos"))
        | uu____19644 -> failwith "Impos"  in
      match uu____19341 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19736 =
              let uu____19743 =
                let uu____19744 =
                  let uu____19751 = mk_imp pre post1  in
                  let uu____19754 =
                    let uu____19755 =
                      let uu____19776 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19776, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19755  in
                  (uu____19751, uu____19754)  in
                FStar_Syntax_Syntax.Tm_meta uu____19744  in
              FStar_Syntax_Syntax.mk uu____19743  in
            uu____19736 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19800 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19800 body
             in
          quant
  