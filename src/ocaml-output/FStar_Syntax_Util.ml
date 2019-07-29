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
          (if
             Prims.op_Negation
               ((FStar_List.length args1) = (FStar_List.length args2))
           then failwith "eq_tm: different arg number on data"
           else ();
           (let uu____3303 = FStar_List.zip args1 args2  in
            FStar_All.pipe_left
              (FStar_List.fold_left
                 (fun acc  ->
                    fun uu____3380  ->
                      match uu____3380 with
                      | ((a1,q1),(a2,q2)) ->
                          let uu____3421 = eq_tm a1 a2  in
                          eq_inj acc uu____3421) Equal) uu____3303))
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3435 =
          let uu____3452 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3452 head_and_args  in
        match uu____3435 with
        | (head1,args1) ->
            let uu____3505 =
              let uu____3522 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3522 head_and_args  in
            (match uu____3505 with
             | (head2,args2) ->
                 let uu____3575 =
                   let uu____3580 =
                     let uu____3581 = un_uinst head1  in
                     uu____3581.FStar_Syntax_Syntax.n  in
                   let uu____3584 =
                     let uu____3585 = un_uinst head2  in
                     uu____3585.FStar_Syntax_Syntax.n  in
                   (uu____3580, uu____3584)  in
                 (match uu____3575 with
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
                  | uu____3612 -> FStar_Pervasives_Native.None))
         in
      let uu____3625 =
        let uu____3630 =
          let uu____3631 = unmeta t11  in uu____3631.FStar_Syntax_Syntax.n
           in
        let uu____3634 =
          let uu____3635 = unmeta t21  in uu____3635.FStar_Syntax_Syntax.n
           in
        (uu____3630, uu____3634)  in
      match uu____3625 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3641,uu____3642) ->
          let uu____3643 = unlazy t11  in eq_tm uu____3643 t21
      | (uu____3644,FStar_Syntax_Syntax.Tm_lazy uu____3645) ->
          let uu____3646 = unlazy t21  in eq_tm t11 uu____3646
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____3649 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3673 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3673
            (fun uu____3721  ->
               match uu____3721 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3736 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3736
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3750 = eq_tm f g  in
          eq_and uu____3750
            (fun uu____3753  ->
               let uu____3754 = eq_univs_list us vs  in equal_if uu____3754)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3756),uu____3757) -> Unknown
      | (uu____3758,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3759)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3762 = FStar_Const.eq_const c d  in equal_iff uu____3762
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3765)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3767))) ->
          let uu____3796 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3796
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3850 =
            let uu____3855 =
              let uu____3856 = un_uinst h1  in
              uu____3856.FStar_Syntax_Syntax.n  in
            let uu____3859 =
              let uu____3860 = un_uinst h2  in
              uu____3860.FStar_Syntax_Syntax.n  in
            (uu____3855, uu____3859)  in
          (match uu____3850 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3866 =
                    let uu____3868 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3868  in
                  FStar_List.mem uu____3866 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3870 ->
               let uu____3875 = eq_tm h1 h2  in
               eq_and uu____3875 (fun uu____3877  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3983 = FStar_List.zip bs1 bs2  in
            let uu____4046 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____4083  ->
                 fun a  ->
                   match uu____4083 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4176  -> branch_matches b1 b2))
              uu____3983 uu____4046
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____4181 = eq_univs u v1  in equal_if uu____4181
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____4195 = eq_quoteinfo q1 q2  in
          eq_and uu____4195 (fun uu____4197  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____4210 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4210 (fun uu____4212  -> eq_tm phi1 phi2)
      | uu____4213 -> Unknown

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
      | ([],uu____4285) -> NotEqual
      | (uu____4316,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____4408 = eq_tm t1 t2  in
             match uu____4408 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4409 = eq_antiquotes a11 a21  in
                 (match uu____4409 with
                  | NotEqual  -> NotEqual
                  | uu____4410 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____4425) -> NotEqual
      | (uu____4432,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4462 -> NotEqual

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
        | (uu____4554,uu____4555) -> false  in
      let uu____4565 = b1  in
      match uu____4565 with
      | (p1,w1,t1) ->
          let uu____4599 = b2  in
          (match uu____4599 with
           | (p2,w2,t2) ->
               let uu____4633 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4633
               then
                 let uu____4636 =
                   (let uu____4640 = eq_tm t1 t2  in uu____4640 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4649 = eq_tm t11 t21  in
                             uu____4649 = Equal) w1 w2)
                    in
                 (if uu____4636 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4714)::a11,(b,uu____4717)::b1) ->
          let uu____4791 = eq_tm a b  in
          (match uu____4791 with
           | Equal  -> eq_args a11 b1
           | uu____4792 -> Unknown)
      | uu____4793 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4829) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4835,uu____4836) ->
        unrefine t2
    | uu____4877 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4885 =
      let uu____4886 = FStar_Syntax_Subst.compress t  in
      uu____4886.FStar_Syntax_Syntax.n  in
    match uu____4885 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4890 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4905) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4910 ->
        let uu____4927 =
          let uu____4928 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4928 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4927 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4991,uu____4992) ->
        is_uvar t1
    | uu____5033 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5042 =
      let uu____5043 = unrefine t  in uu____5043.FStar_Syntax_Syntax.n  in
    match uu____5042 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____5049) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5075) -> is_unit t1
    | uu____5080 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5089 =
      let uu____5090 = FStar_Syntax_Subst.compress t  in
      uu____5090.FStar_Syntax_Syntax.n  in
    match uu____5089 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5095 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5104 =
      let uu____5105 = unrefine t  in uu____5105.FStar_Syntax_Syntax.n  in
    match uu____5104 with
    | FStar_Syntax_Syntax.Tm_type uu____5109 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____5113) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5139) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____5144,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____5166 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5175 =
      let uu____5176 = FStar_Syntax_Subst.compress e  in
      uu____5176.FStar_Syntax_Syntax.n  in
    match uu____5175 with
    | FStar_Syntax_Syntax.Tm_abs uu____5180 -> true
    | uu____5200 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5209 =
      let uu____5210 = FStar_Syntax_Subst.compress t  in
      uu____5210.FStar_Syntax_Syntax.n  in
    match uu____5209 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5214 -> true
    | uu____5230 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5240) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5246,uu____5247) ->
        pre_typ t2
    | uu____5288 -> t1
  
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
      let uu____5313 =
        let uu____5314 = un_uinst typ1  in uu____5314.FStar_Syntax_Syntax.n
         in
      match uu____5313 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5379 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5409 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5430,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5437) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5442,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5453,uu____5454,uu____5455,uu____5456,uu____5457) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5467,uu____5468,uu____5469,uu____5470) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5476,uu____5477,uu____5478,uu____5479,uu____5480) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5488,uu____5489) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5491,uu____5492) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5494 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5495 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5496 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5510 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___11_5536  ->
    match uu___11_5536 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5550 'Auu____5551 .
    ('Auu____5550 FStar_Syntax_Syntax.syntax * 'Auu____5551) ->
      FStar_Range.range
  =
  fun uu____5562  ->
    match uu____5562 with | (hd1,uu____5570) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5584 'Auu____5585 .
    ('Auu____5584 FStar_Syntax_Syntax.syntax * 'Auu____5585) Prims.list ->
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
      | uu____5683 ->
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
      let uu____5742 =
        FStar_List.map
          (fun uu____5769  ->
             match uu____5769 with
             | (bv,aq) ->
                 let uu____5788 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5788, aq)) bs
         in
      mk_app f uu____5742
  
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
          let uu____5838 = FStar_Ident.range_of_lid l  in
          let uu____5839 =
            let uu____5848 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5848  in
          uu____5839 FStar_Pervasives_Native.None uu____5838
      | uu____5853 ->
          let e =
            let uu____5867 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5867 args  in
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
          let uu____5944 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5944
          then
            let uu____5947 =
              let uu____5953 =
                let uu____5955 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5955  in
              let uu____5958 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5953, uu____5958)  in
            FStar_Ident.mk_ident uu____5947
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___993_5963 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___993_5963.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___993_5963.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5964 = mk_field_projector_name_from_ident lid nm  in
        (uu____5964, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5976) -> ses
    | uu____5985 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____5996 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____6009 = FStar_Syntax_Unionfind.find uv  in
      match uu____6009 with
      | FStar_Pervasives_Native.Some uu____6012 ->
          let uu____6013 =
            let uu____6015 =
              let uu____6017 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____6017  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____6015  in
          failwith uu____6013
      | uu____6022 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____6105 -> q1 = q2
  
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
              let uu____6151 =
                let uu___1054_6152 = rc  in
                let uu____6153 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1054_6152.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6153;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1054_6152.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6151
           in
        match bs with
        | [] -> t
        | uu____6170 ->
            let body =
              let uu____6172 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6172  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6202 =
                   let uu____6209 =
                     let uu____6210 =
                       let uu____6229 =
                         let uu____6238 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6238 bs'  in
                       let uu____6253 = close_lopt lopt'  in
                       (uu____6229, t1, uu____6253)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6210  in
                   FStar_Syntax_Syntax.mk uu____6209  in
                 uu____6202 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6268 ->
                 let uu____6269 =
                   let uu____6276 =
                     let uu____6277 =
                       let uu____6296 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6305 = close_lopt lopt  in
                       (uu____6296, body, uu____6305)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6277  in
                   FStar_Syntax_Syntax.mk uu____6276  in
                 uu____6269 FStar_Pervasives_Native.None
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
      | uu____6361 ->
          let uu____6370 =
            let uu____6377 =
              let uu____6378 =
                let uu____6393 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6402 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6393, uu____6402)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6378  in
            FStar_Syntax_Syntax.mk uu____6377  in
          uu____6370 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6451 =
        let uu____6452 = FStar_Syntax_Subst.compress t  in
        uu____6452.FStar_Syntax_Syntax.n  in
      match uu____6451 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6482) ->
               let uu____6491 =
                 let uu____6492 = FStar_Syntax_Subst.compress tres  in
                 uu____6492.FStar_Syntax_Syntax.n  in
               (match uu____6491 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6535 -> t)
           | uu____6536 -> t)
      | uu____6537 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6555 =
        let uu____6556 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6556 t.FStar_Syntax_Syntax.pos  in
      let uu____6557 =
        let uu____6564 =
          let uu____6565 =
            let uu____6572 =
              let uu____6575 =
                let uu____6576 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6576]  in
              FStar_Syntax_Subst.close uu____6575 t  in
            (b, uu____6572)  in
          FStar_Syntax_Syntax.Tm_refine uu____6565  in
        FStar_Syntax_Syntax.mk uu____6564  in
      uu____6557 FStar_Pervasives_Native.None uu____6555
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let k1 = unascribe k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____6656 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6656 with
         | (bs1,c1) ->
             let uu____6675 = is_total_comp c1  in
             if uu____6675
             then
               let uu____6690 = arrow_formals_comp (comp_result c1)  in
               (match uu____6690 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6757;
           FStar_Syntax_Syntax.index = uu____6758;
           FStar_Syntax_Syntax.sort = s;_},uu____6760)
        ->
        let rec aux s1 k2 =
          let uu____6791 =
            let uu____6792 = FStar_Syntax_Subst.compress s1  in
            uu____6792.FStar_Syntax_Syntax.n  in
          match uu____6791 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6807 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6822;
                 FStar_Syntax_Syntax.index = uu____6823;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6825)
              -> aux s2 k2
          | uu____6833 ->
              let uu____6834 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6834)
           in
        aux s k1
    | uu____6849 ->
        let uu____6850 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6850)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6885 = arrow_formals_comp k  in
    match uu____6885 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7027 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7027 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____7051 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___12_7060  ->
                         match uu___12_7060 with
                         | FStar_Syntax_Syntax.DECREASES uu____7062 -> true
                         | uu____7066 -> false))
                  in
               (match uu____7051 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7101 ->
                    let uu____7104 = is_total_comp c1  in
                    if uu____7104
                    then
                      let uu____7123 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7123 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7216;
             FStar_Syntax_Syntax.index = uu____7217;
             FStar_Syntax_Syntax.sort = k2;_},uu____7219)
          -> arrow_until_decreases k2
      | uu____7227 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7248 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7248 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7302 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7323 =
                 FStar_Common.tabulate n_univs (fun uu____7329  -> false)  in
               let uu____7332 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7357  ->
                         match uu____7357 with
                         | (x,uu____7366) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7323 uu____7332)
           in
        ((n_univs + (FStar_List.length bs)), uu____7302)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7422 =
            let uu___1176_7423 = rc  in
            let uu____7424 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1176_7423.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7424;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1176_7423.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7422
      | uu____7433 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7467 =
        let uu____7468 =
          let uu____7471 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7471  in
        uu____7468.FStar_Syntax_Syntax.n  in
      match uu____7467 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7517 = aux t2 what  in
          (match uu____7517 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7589 -> ([], t1, abs_body_lcomp)  in
    let uu____7606 = aux t FStar_Pervasives_Native.None  in
    match uu____7606 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7654 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7654 with
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
                    | (FStar_Pervasives_Native.None ,uu____7817) -> def
                    | (uu____7828,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7840) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _7856  ->
                                  FStar_Syntax_Syntax.U_name _7856))
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
            let uu____7938 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7938 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7973 ->
            let t' = arrow binders c  in
            let uu____7985 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____7985 with
             | (uvs1,t'1) ->
                 let uu____8006 =
                   let uu____8007 = FStar_Syntax_Subst.compress t'1  in
                   uu____8007.FStar_Syntax_Syntax.n  in
                 (match uu____8006 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8056 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____8081 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8092 -> false
  
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
      let uu____8155 =
        let uu____8156 = pre_typ t  in uu____8156.FStar_Syntax_Syntax.n  in
      match uu____8155 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8161 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8175 =
        let uu____8176 = pre_typ t  in uu____8176.FStar_Syntax_Syntax.n  in
      match uu____8175 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8180 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8182) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8208) ->
          is_constructed_typ t1 lid
      | uu____8213 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8226 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8227 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8228 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8230) -> get_tycon t2
    | uu____8255 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8263 =
      let uu____8264 = un_uinst t  in uu____8264.FStar_Syntax_Syntax.n  in
    match uu____8263 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8269 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8283 =
        let uu____8287 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8287  in
      match uu____8283 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8319 -> false
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
  fun uu____8338  ->
    let u =
      let uu____8344 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _8361  -> FStar_Syntax_Syntax.U_unif _8361)
        uu____8344
       in
    let uu____8362 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8362, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8375 = eq_tm a a'  in
      match uu____8375 with | Equal  -> true | uu____8378 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8383 =
    let uu____8390 =
      let uu____8391 =
        let uu____8392 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8392
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8391  in
    FStar_Syntax_Syntax.mk uu____8390  in
  uu____8383 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8504 =
            let uu____8507 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8508 =
              let uu____8515 =
                let uu____8516 =
                  let uu____8533 =
                    let uu____8544 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8553 =
                      let uu____8564 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8564]  in
                    uu____8544 :: uu____8553  in
                  (tand, uu____8533)  in
                FStar_Syntax_Syntax.Tm_app uu____8516  in
              FStar_Syntax_Syntax.mk uu____8515  in
            uu____8508 FStar_Pervasives_Native.None uu____8507  in
          FStar_Pervasives_Native.Some uu____8504
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8641 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8642 =
          let uu____8649 =
            let uu____8650 =
              let uu____8667 =
                let uu____8678 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8687 =
                  let uu____8698 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8698]  in
                uu____8678 :: uu____8687  in
              (op_t, uu____8667)  in
            FStar_Syntax_Syntax.Tm_app uu____8650  in
          FStar_Syntax_Syntax.mk uu____8649  in
        uu____8642 FStar_Pervasives_Native.None uu____8641
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8755 =
      let uu____8762 =
        let uu____8763 =
          let uu____8780 =
            let uu____8791 = FStar_Syntax_Syntax.as_arg phi  in [uu____8791]
             in
          (t_not, uu____8780)  in
        FStar_Syntax_Syntax.Tm_app uu____8763  in
      FStar_Syntax_Syntax.mk uu____8762  in
    uu____8755 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____8988 =
      let uu____8995 =
        let uu____8996 =
          let uu____9013 =
            let uu____9024 = FStar_Syntax_Syntax.as_arg e  in [uu____9024]
             in
          (b2t_v, uu____9013)  in
        FStar_Syntax_Syntax.Tm_app uu____8996  in
      FStar_Syntax_Syntax.mk uu____8995  in
    uu____8988 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9071 = head_and_args e  in
    match uu____9071 with
    | (hd1,args) ->
        let uu____9116 =
          let uu____9131 =
            let uu____9132 = FStar_Syntax_Subst.compress hd1  in
            uu____9132.FStar_Syntax_Syntax.n  in
          (uu____9131, args)  in
        (match uu____9116 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9149)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9184 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9206 =
      let uu____9207 = unmeta t  in uu____9207.FStar_Syntax_Syntax.n  in
    match uu____9206 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9212 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9235 = is_t_true t1  in
      if uu____9235
      then t2
      else
        (let uu____9242 = is_t_true t2  in
         if uu____9242 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9270 = is_t_true t1  in
      if uu____9270
      then t_true
      else
        (let uu____9277 = is_t_true t2  in
         if uu____9277 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9306 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9307 =
        let uu____9314 =
          let uu____9315 =
            let uu____9332 =
              let uu____9343 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9352 =
                let uu____9363 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9363]  in
              uu____9343 :: uu____9352  in
            (teq, uu____9332)  in
          FStar_Syntax_Syntax.Tm_app uu____9315  in
        FStar_Syntax_Syntax.mk uu____9314  in
      uu____9307 FStar_Pervasives_Native.None uu____9306
  
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
          let uu____9430 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9431 =
            let uu____9438 =
              let uu____9439 =
                let uu____9456 =
                  let uu____9467 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9476 =
                    let uu____9487 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9496 =
                      let uu____9507 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9507]  in
                    uu____9487 :: uu____9496  in
                  uu____9467 :: uu____9476  in
                (eq_inst, uu____9456)  in
              FStar_Syntax_Syntax.Tm_app uu____9439  in
            FStar_Syntax_Syntax.mk uu____9438  in
          uu____9431 FStar_Pervasives_Native.None uu____9430
  
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
        let uu____9584 =
          let uu____9591 =
            let uu____9592 =
              let uu____9609 =
                let uu____9620 = FStar_Syntax_Syntax.iarg t  in
                let uu____9629 =
                  let uu____9640 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9649 =
                    let uu____9660 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9660]  in
                  uu____9640 :: uu____9649  in
                uu____9620 :: uu____9629  in
              (t_has_type1, uu____9609)  in
            FStar_Syntax_Syntax.Tm_app uu____9592  in
          FStar_Syntax_Syntax.mk uu____9591  in
        uu____9584 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9737 =
          let uu____9744 =
            let uu____9745 =
              let uu____9762 =
                let uu____9773 = FStar_Syntax_Syntax.iarg t  in
                let uu____9782 =
                  let uu____9793 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9793]  in
                uu____9773 :: uu____9782  in
              (t_with_type1, uu____9762)  in
            FStar_Syntax_Syntax.Tm_app uu____9745  in
          FStar_Syntax_Syntax.mk uu____9744  in
        uu____9737 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9840 =
    let uu____9847 =
      let uu____9848 =
        let uu____9855 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9855, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9848  in
    FStar_Syntax_Syntax.mk uu____9847  in
  uu____9840 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____9870 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____9883 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____9894 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____9870 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____9915  -> c0)
  
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
        let uu____9998 =
          let uu____10005 =
            let uu____10006 =
              let uu____10023 =
                let uu____10034 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____10043 =
                  let uu____10054 =
                    let uu____10063 =
                      let uu____10064 =
                        let uu____10065 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10065]  in
                      abs uu____10064 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10063  in
                  [uu____10054]  in
                uu____10034 :: uu____10043  in
              (fa, uu____10023)  in
            FStar_Syntax_Syntax.Tm_app uu____10006  in
          FStar_Syntax_Syntax.mk uu____10005  in
        uu____9998 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10192 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10192
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10211 -> true
    | uu____10213 -> false
  
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
          let uu____10260 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10260, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10289 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10289, FStar_Pervasives_Native.None, t2)  in
        let uu____10303 =
          let uu____10304 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10304  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10303
  
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
      let uu____10380 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10383 =
        let uu____10394 = FStar_Syntax_Syntax.as_arg p  in [uu____10394]  in
      mk_app uu____10380 uu____10383
  
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
      let uu____10434 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10437 =
        let uu____10448 = FStar_Syntax_Syntax.as_arg p  in [uu____10448]  in
      mk_app uu____10434 uu____10437
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10483 = head_and_args t  in
    match uu____10483 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____10532 =
          let uu____10547 =
            let uu____10548 = FStar_Syntax_Subst.compress head3  in
            uu____10548.FStar_Syntax_Syntax.n  in
          (uu____10547, args)  in
        (match uu____10532 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10567)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10633 =
                    let uu____10638 =
                      let uu____10639 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10639]  in
                    FStar_Syntax_Subst.open_term uu____10638 p  in
                  (match uu____10633 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10696 -> failwith "impossible"  in
                       let uu____10704 =
                         let uu____10706 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10706
                          in
                       if uu____10704
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10722 -> FStar_Pervasives_Native.None)
         | uu____10725 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10756 = head_and_args t  in
    match uu____10756 with
    | (head1,args) ->
        let uu____10807 =
          let uu____10822 =
            let uu____10823 = FStar_Syntax_Subst.compress head1  in
            uu____10823.FStar_Syntax_Syntax.n  in
          (uu____10822, args)  in
        (match uu____10807 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10845;
               FStar_Syntax_Syntax.vars = uu____10846;_},u::[]),(t1,uu____10849)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10896 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10931 = head_and_args t  in
    match uu____10931 with
    | (head1,args) ->
        let uu____10982 =
          let uu____10997 =
            let uu____10998 = FStar_Syntax_Subst.compress head1  in
            uu____10998.FStar_Syntax_Syntax.n  in
          (uu____10997, args)  in
        (match uu____10982 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____11020;
               FStar_Syntax_Syntax.vars = uu____11021;_},u::[]),(t1,uu____11024)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11071 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11099 =
      let uu____11116 = unmeta t  in head_and_args uu____11116  in
    match uu____11099 with
    | (head1,uu____11119) ->
        let uu____11144 =
          let uu____11145 = un_uinst head1  in
          uu____11145.FStar_Syntax_Syntax.n  in
        (match uu____11144 with
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
         | uu____11150 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11170 =
      let uu____11183 =
        let uu____11184 = FStar_Syntax_Subst.compress t  in
        uu____11184.FStar_Syntax_Syntax.n  in
      match uu____11183 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____11314 =
            let uu____11325 =
              let uu____11326 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____11326  in
            (b, uu____11325)  in
          FStar_Pervasives_Native.Some uu____11314
      | uu____11343 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____11170
      (fun uu____11381  ->
         match uu____11381 with
         | (b,c) ->
             let uu____11418 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11418 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11481 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11518 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11518
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11570 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11613 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11654 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____12040) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____12052) ->
          unmeta_monadic t
      | uu____12065 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12134 =
        match uu____12134 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12172  ->
                   match uu____12172 with
                   | (lid,out_lid) ->
                       let uu____12181 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12181
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12208 = head_and_args t  in
      match uu____12208 with
      | (hd1,args) ->
          let uu____12253 =
            let uu____12254 = un_uinst hd1  in
            uu____12254.FStar_Syntax_Syntax.n  in
          (match uu____12253 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12260 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12269 = un_squash t  in
      FStar_Util.bind_opt uu____12269
        (fun t1  ->
           let uu____12285 = head_and_args' t1  in
           match uu____12285 with
           | (hd1,args) ->
               let uu____12324 =
                 let uu____12325 = un_uinst hd1  in
                 uu____12325.FStar_Syntax_Syntax.n  in
               (match uu____12324 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12331 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12372,pats)) ->
          let uu____12410 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12410)
      | uu____12423 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12490 = head_and_args t1  in
        match uu____12490 with
        | (t2,args) ->
            let uu____12545 = un_uinst t2  in
            let uu____12546 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12587  ->
                      match uu____12587 with
                      | (t3,imp) ->
                          let uu____12606 = unascribe t3  in
                          (uu____12606, imp)))
               in
            (uu____12545, uu____12546)
         in
      let rec aux qopt out t1 =
        let uu____12657 = let uu____12681 = flat t1  in (qopt, uu____12681)
           in
        match uu____12657 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12721;
                 FStar_Syntax_Syntax.vars = uu____12722;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12725);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12726;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12727;_},uu____12728)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12830;
                 FStar_Syntax_Syntax.vars = uu____12831;_},uu____12832::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12835);
                  FStar_Syntax_Syntax.pos = uu____12836;
                  FStar_Syntax_Syntax.vars = uu____12837;_},uu____12838)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12955;
               FStar_Syntax_Syntax.vars = uu____12956;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12959);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12960;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12961;_},uu____12962)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13055 =
              let uu____13059 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13059  in
            aux uu____13055 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13069;
               FStar_Syntax_Syntax.vars = uu____13070;_},uu____13071::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____13074);
                FStar_Syntax_Syntax.pos = uu____13075;
                FStar_Syntax_Syntax.vars = uu____13076;_},uu____13077)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13186 =
              let uu____13190 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13190  in
            aux uu____13186 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13200) ->
            let bs = FStar_List.rev out  in
            let uu____13253 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13253 with
             | (bs1,t2) ->
                 let uu____13262 = patterns t2  in
                 (match uu____13262 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13312 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13367 = un_squash t  in
      FStar_Util.bind_opt uu____13367
        (fun t1  ->
           let uu____13382 = arrow_one t1  in
           match uu____13382 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13397 =
                 let uu____13399 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13399  in
               if uu____13397
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13409 = comp_to_comp_typ_nouniv c  in
                    uu____13409.FStar_Syntax_Syntax.result_typ  in
                  let uu____13410 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13410
                  then
                    let uu____13417 = patterns q  in
                    match uu____13417 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13480 =
                       let uu____13481 =
                         let uu____13486 =
                           let uu____13487 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13498 =
                             let uu____13509 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13509]  in
                           uu____13487 :: uu____13498  in
                         (FStar_Parser_Const.imp_lid, uu____13486)  in
                       BaseConn uu____13481  in
                     FStar_Pervasives_Native.Some uu____13480))
           | uu____13542 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13550 = un_squash t  in
      FStar_Util.bind_opt uu____13550
        (fun t1  ->
           let uu____13581 = head_and_args' t1  in
           match uu____13581 with
           | (hd1,args) ->
               let uu____13620 =
                 let uu____13635 =
                   let uu____13636 = un_uinst hd1  in
                   uu____13636.FStar_Syntax_Syntax.n  in
                 (uu____13635, args)  in
               (match uu____13620 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13653)::(a2,uu____13655)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13706 =
                      let uu____13707 = FStar_Syntax_Subst.compress a2  in
                      uu____13707.FStar_Syntax_Syntax.n  in
                    (match uu____13706 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13714) ->
                         let uu____13749 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13749 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13802 -> failwith "impossible"  in
                              let uu____13810 = patterns q1  in
                              (match uu____13810 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13871 -> FStar_Pervasives_Native.None)
                | uu____13872 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13895 = destruct_sq_forall phi  in
          (match uu____13895 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13905  -> FStar_Pervasives_Native.Some _13905)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13912 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13918 = destruct_sq_exists phi  in
          (match uu____13918 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13928  -> FStar_Pervasives_Native.Some _13928)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13935 -> f1)
      | uu____13938 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13942 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13942
      (fun uu____13947  ->
         let uu____13948 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13948
           (fun uu____13953  ->
              let uu____13954 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13954
                (fun uu____13959  ->
                   let uu____13960 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13960
                     (fun uu____13965  ->
                        let uu____13966 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13966
                          (fun uu____13970  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13988 =
            let uu____13993 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13993  in
          let uu____13994 =
            let uu____13995 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13995  in
          let uu____13998 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13988 a.FStar_Syntax_Syntax.action_univs uu____13994
            FStar_Parser_Const.effect_Tot_lid uu____13998 [] pos
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
    let uu____14024 =
      let uu____14031 =
        let uu____14032 =
          let uu____14049 =
            let uu____14060 = FStar_Syntax_Syntax.as_arg t  in [uu____14060]
             in
          (reify_1, uu____14049)  in
        FStar_Syntax_Syntax.Tm_app uu____14032  in
      FStar_Syntax_Syntax.mk uu____14031  in
    uu____14024 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14112 =
        let uu____14119 =
          let uu____14120 =
            let uu____14121 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14121  in
          FStar_Syntax_Syntax.Tm_constant uu____14120  in
        FStar_Syntax_Syntax.mk uu____14119  in
      uu____14112 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14123 =
      let uu____14130 =
        let uu____14131 =
          let uu____14148 =
            let uu____14159 = FStar_Syntax_Syntax.as_arg t  in [uu____14159]
             in
          (reflect_, uu____14148)  in
        FStar_Syntax_Syntax.Tm_app uu____14131  in
      FStar_Syntax_Syntax.mk uu____14130  in
    uu____14123 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14203 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14228 = unfold_lazy i  in delta_qualifier uu____14228
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14230 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14231 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14232 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14255 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14268 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14269 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14276 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14277 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14293) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14298;
           FStar_Syntax_Syntax.index = uu____14299;
           FStar_Syntax_Syntax.sort = t2;_},uu____14301)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14310) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14316,uu____14317) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14359) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14384,t2,uu____14386) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14411,t2) -> delta_qualifier t2
  
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
    let uu____14450 = delta_qualifier t  in incr_delta_depth uu____14450
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14458 =
      let uu____14459 = FStar_Syntax_Subst.compress t  in
      uu____14459.FStar_Syntax_Syntax.n  in
    match uu____14458 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14464 -> false
  
let rec apply_last :
  'Auu____14473 .
    ('Auu____14473 -> 'Auu____14473) ->
      'Auu____14473 Prims.list -> 'Auu____14473 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14499 = f a  in [uu____14499]
      | x::xs -> let uu____14504 = apply_last f xs  in x :: uu____14504
  
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
          let uu____14559 =
            let uu____14566 =
              let uu____14567 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14567  in
            FStar_Syntax_Syntax.mk uu____14566  in
          uu____14559 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____14581 =
            let uu____14586 =
              let uu____14587 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14587
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14586 args  in
          uu____14581 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14601 =
            let uu____14606 =
              let uu____14607 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14607
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14606 args  in
          uu____14601 FStar_Pervasives_Native.None pos  in
        let uu____14608 =
          let uu____14609 =
            let uu____14610 = FStar_Syntax_Syntax.iarg typ  in [uu____14610]
             in
          nil uu____14609 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14644 =
                 let uu____14645 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14654 =
                   let uu____14665 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14674 =
                     let uu____14685 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14685]  in
                   uu____14665 :: uu____14674  in
                 uu____14645 :: uu____14654  in
               cons1 uu____14644 t.FStar_Syntax_Syntax.pos) l uu____14608
  
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
        | uu____14794 -> false
  
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
          | uu____14908 -> false
  
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
        | uu____15074 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15112 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15112
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
        let t11 = let uu____15334 = unmeta_safe t1  in canon_app uu____15334
           in
        let t21 = let uu____15340 = unmeta_safe t2  in canon_app uu____15340
           in
        let uu____15343 =
          let uu____15348 =
            let uu____15349 =
              let uu____15352 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15352  in
            uu____15349.FStar_Syntax_Syntax.n  in
          let uu____15353 =
            let uu____15354 =
              let uu____15357 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15357  in
            uu____15354.FStar_Syntax_Syntax.n  in
          (uu____15348, uu____15353)  in
        match uu____15343 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15359,uu____15360) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15369,FStar_Syntax_Syntax.Tm_uinst uu____15370) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15379,uu____15380) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15405,FStar_Syntax_Syntax.Tm_delayed uu____15406) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15431,uu____15432) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15461,FStar_Syntax_Syntax.Tm_ascribed uu____15462) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15501 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15501
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15506 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15506
        | (FStar_Syntax_Syntax.Tm_type
           uu____15509,FStar_Syntax_Syntax.Tm_type uu____15510) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15568 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15568) &&
              (let uu____15578 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15578)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15627 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15627) &&
              (let uu____15637 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15637)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15654 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15654) &&
              (let uu____15658 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15658)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15715 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15715) &&
              (let uu____15719 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15719)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15808 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15808) &&
              (let uu____15812 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15812)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15829,uu____15830) ->
            let uu____15831 =
              let uu____15833 = unlazy t11  in
              term_eq_dbg dbg uu____15833 t21  in
            check "lazy_l" uu____15831
        | (uu____15835,FStar_Syntax_Syntax.Tm_lazy uu____15836) ->
            let uu____15837 =
              let uu____15839 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15839  in
            check "lazy_r" uu____15837
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15884 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15884))
              &&
              (let uu____15888 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15888)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15892),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15894)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15952 =
               let uu____15954 = eq_quoteinfo qi1 qi2  in uu____15954 = Equal
                in
             check "tm_quoted qi" uu____15952) &&
              (let uu____15957 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15957)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15987 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15987) &&
                   (let uu____15991 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15991)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____16010 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____16010) &&
                    (let uu____16014 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____16014))
                   &&
                   (let uu____16018 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____16018)
             | uu____16021 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____16027) -> fail "unk"
        | (uu____16029,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____16031,uu____16032) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____16034,uu____16035) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____16037,uu____16038) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____16040,uu____16041) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____16043,uu____16044) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____16046,uu____16047) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____16067,uu____16068) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____16084,uu____16085) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____16093,uu____16094) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____16112,uu____16113) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16137,uu____16138) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16153,uu____16154) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16168,uu____16169) ->
            fail "bottom"
        | (uu____16177,FStar_Syntax_Syntax.Tm_bvar uu____16178) ->
            fail "bottom"
        | (uu____16180,FStar_Syntax_Syntax.Tm_name uu____16181) ->
            fail "bottom"
        | (uu____16183,FStar_Syntax_Syntax.Tm_fvar uu____16184) ->
            fail "bottom"
        | (uu____16186,FStar_Syntax_Syntax.Tm_constant uu____16187) ->
            fail "bottom"
        | (uu____16189,FStar_Syntax_Syntax.Tm_type uu____16190) ->
            fail "bottom"
        | (uu____16192,FStar_Syntax_Syntax.Tm_abs uu____16193) ->
            fail "bottom"
        | (uu____16213,FStar_Syntax_Syntax.Tm_arrow uu____16214) ->
            fail "bottom"
        | (uu____16230,FStar_Syntax_Syntax.Tm_refine uu____16231) ->
            fail "bottom"
        | (uu____16239,FStar_Syntax_Syntax.Tm_app uu____16240) ->
            fail "bottom"
        | (uu____16258,FStar_Syntax_Syntax.Tm_match uu____16259) ->
            fail "bottom"
        | (uu____16283,FStar_Syntax_Syntax.Tm_let uu____16284) ->
            fail "bottom"
        | (uu____16299,FStar_Syntax_Syntax.Tm_uvar uu____16300) ->
            fail "bottom"
        | (uu____16314,FStar_Syntax_Syntax.Tm_meta uu____16315) ->
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
               let uu____16350 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16350)
          (fun q1  ->
             fun q2  ->
               let uu____16362 =
                 let uu____16364 = eq_aqual q1 q2  in uu____16364 = Equal  in
               check "arg qual" uu____16362) a1 a2

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
               let uu____16389 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16389)
          (fun q1  ->
             fun q2  ->
               let uu____16401 =
                 let uu____16403 = eq_aqual q1 q2  in uu____16403 = Equal  in
               check "binder qual" uu____16401) b1 b2

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
        ((let uu____16423 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16423) &&
           (let uu____16427 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16427))
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
    fun uu____16437  ->
      fun uu____16438  ->
        match (uu____16437, uu____16438) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16565 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16565) &&
               (let uu____16569 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16569))
              &&
              (let uu____16573 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16615 -> false  in
               check "branch when" uu____16573)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16636 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16636) &&
           (let uu____16645 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16645))
          &&
          (let uu____16649 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16649)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16666 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16666 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16720 ->
        let uu____16743 =
          let uu____16745 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16745  in
        Prims.int_one + uu____16743
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16748 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16748
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16752 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16752
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16761 = sizeof t1  in (FStar_List.length us) + uu____16761
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16765) ->
        let uu____16790 = sizeof t1  in
        let uu____16792 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16807  ->
                 match uu____16807 with
                 | (bv,uu____16817) ->
                     let uu____16822 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16822) Prims.int_zero bs
           in
        uu____16790 + uu____16792
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____16851 = sizeof hd1  in
        let uu____16853 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16868  ->
                 match uu____16868 with
                 | (arg,uu____16878) ->
                     let uu____16883 = sizeof arg  in acc + uu____16883)
            Prims.int_zero args
           in
        uu____16851 + uu____16853
    | uu____16886 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16900 =
        let uu____16901 = un_uinst t  in uu____16901.FStar_Syntax_Syntax.n
         in
      match uu____16900 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16906 -> false
  
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
        let uu____16950 = FStar_Options.set_options s  in
        match uu____16950 with
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
          ((let uu____16964 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16964 (fun a1  -> ()));
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
          let uu____16979 = FStar_Options.internal_pop ()  in
          if uu____16979
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
    | FStar_Syntax_Syntax.Tm_delayed uu____17011 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17038 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17053 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17054 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17055 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17064) ->
        let uu____17089 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17089 with
         | (bs1,t2) ->
             let uu____17098 =
               FStar_List.collect
                 (fun uu____17110  ->
                    match uu____17110 with
                    | (b,uu____17120) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17125 = unbound_variables t2  in
             FStar_List.append uu____17098 uu____17125)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17150 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17150 with
         | (bs1,c1) ->
             let uu____17159 =
               FStar_List.collect
                 (fun uu____17171  ->
                    match uu____17171 with
                    | (b,uu____17181) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17186 = unbound_variables_comp c1  in
             FStar_List.append uu____17159 uu____17186)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17195 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17195 with
         | (bs,t2) ->
             let uu____17218 =
               FStar_List.collect
                 (fun uu____17230  ->
                    match uu____17230 with
                    | (b1,uu____17240) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17245 = unbound_variables t2  in
             FStar_List.append uu____17218 uu____17245)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17274 =
          FStar_List.collect
            (fun uu____17288  ->
               match uu____17288 with
               | (x,uu____17300) -> unbound_variables x) args
           in
        let uu____17309 = unbound_variables t1  in
        FStar_List.append uu____17274 uu____17309
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17350 = unbound_variables t1  in
        let uu____17353 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17368 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17368 with
                  | (p,wopt,t2) ->
                      let uu____17390 = unbound_variables t2  in
                      let uu____17393 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17390 uu____17393))
           in
        FStar_List.append uu____17350 uu____17353
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17407) ->
        let uu____17448 = unbound_variables t1  in
        let uu____17451 =
          let uu____17454 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17485 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17454 uu____17485  in
        FStar_List.append uu____17448 uu____17451
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17526 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17529 =
          let uu____17532 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17535 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17540 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17542 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17542 with
                 | (uu____17563,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17532 uu____17535  in
        FStar_List.append uu____17526 uu____17529
    | FStar_Syntax_Syntax.Tm_let ((uu____17565,lbs),t1) ->
        let uu____17585 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17585 with
         | (lbs1,t2) ->
             let uu____17600 = unbound_variables t2  in
             let uu____17603 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17610 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17613 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17610 uu____17613) lbs1
                in
             FStar_List.append uu____17600 uu____17603)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17630 = unbound_variables t1  in
        let uu____17633 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17638,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17693  ->
                      match uu____17693 with
                      | (a,uu____17705) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17714,uu____17715,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17721,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17727 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17736 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17737 -> []  in
        FStar_List.append uu____17630 uu____17633

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17744) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17754) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17764 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17767 =
          FStar_List.collect
            (fun uu____17781  ->
               match uu____17781 with
               | (a,uu____17793) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17764 uu____17767

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
            let uu____17908 = head_and_args h  in
            (match uu____17908 with
             | (head1,args) ->
                 let uu____17969 =
                   let uu____17970 = FStar_Syntax_Subst.compress head1  in
                   uu____17970.FStar_Syntax_Syntax.n  in
                 (match uu____17969 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18023 -> aux (h :: acc) t))
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
      let uu____18047 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18047 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2519_18089 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2519_18089.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2519_18089.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2519_18089.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2519_18089.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18097 =
      let uu____18098 = FStar_Syntax_Subst.compress t  in
      uu____18098.FStar_Syntax_Syntax.n  in
    match uu____18097 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18102,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18130)::uu____18131 ->
                  let pats' = unmeta pats  in
                  let uu____18191 = head_and_args pats'  in
                  (match uu____18191 with
                   | (head1,uu____18210) ->
                       let uu____18235 =
                         let uu____18236 = un_uinst head1  in
                         uu____18236.FStar_Syntax_Syntax.n  in
                       (match uu____18235 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18241 -> false))
              | uu____18243 -> false)
         | uu____18255 -> false)
    | uu____18257 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18273 =
      let uu____18290 = unmeta e  in head_and_args uu____18290  in
    match uu____18273 with
    | (head1,args) ->
        let uu____18321 =
          let uu____18336 =
            let uu____18337 = un_uinst head1  in
            uu____18337.FStar_Syntax_Syntax.n  in
          (uu____18336, args)  in
        (match uu____18321 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18355) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18379::(hd1,uu____18381)::(tl1,uu____18383)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18450 =
               let uu____18453 =
                 let uu____18456 = list_elements tl1  in
                 FStar_Util.must uu____18456  in
               hd1 :: uu____18453  in
             FStar_Pervasives_Native.Some uu____18450
         | uu____18465 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18494 =
      let uu____18495 = FStar_Syntax_Subst.compress t  in
      uu____18495.FStar_Syntax_Syntax.n  in
    match uu____18494 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18502) ->
        let uu____18537 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18537 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18571 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18571
             then
               let uu____18578 =
                 let uu____18589 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18589]  in
               mk_app t uu____18578
             else e1)
    | uu____18616 ->
        let uu____18617 =
          let uu____18628 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18628]  in
        mk_app t uu____18617
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18683 = list_elements e  in
        match uu____18683 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18714 =
          let uu____18731 = unmeta p  in
          FStar_All.pipe_right uu____18731 head_and_args  in
        match uu____18714 with
        | (head1,args) ->
            let uu____18782 =
              let uu____18797 =
                let uu____18798 = un_uinst head1  in
                uu____18798.FStar_Syntax_Syntax.n  in
              (uu____18797, args)  in
            (match uu____18782 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18820,uu____18821)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18873 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____18928 =
            let uu____18945 = unmeta t1  in
            FStar_All.pipe_right uu____18945 head_and_args  in
          match uu____18928 with
          | (head1,args) ->
              let uu____18992 =
                let uu____19007 =
                  let uu____19008 = un_uinst head1  in
                  uu____19008.FStar_Syntax_Syntax.n  in
                (uu____19007, args)  in
              (match uu____18992 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19027)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19064 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19094 = smt_pat_or1 t1  in
            (match uu____19094 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19116 = list_elements1 e  in
                 FStar_All.pipe_right uu____19116
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19146 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19146
                           (FStar_List.map one_pat)))
             | uu____19169 ->
                 let uu____19174 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19174])
        | uu____19225 ->
            let uu____19228 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19228]
         in
      let uu____19279 =
        let uu____19312 =
          let uu____19313 = FStar_Syntax_Subst.compress t  in
          uu____19313.FStar_Syntax_Syntax.n  in
        match uu____19312 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19370 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19370 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19441;
                        FStar_Syntax_Syntax.effect_name = uu____19442;
                        FStar_Syntax_Syntax.result_typ = uu____19443;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19445)::(post,uu____19447)::(pats,uu____19449)::[];
                        FStar_Syntax_Syntax.flags = uu____19450;_}
                      ->
                      let uu____19511 = lemma_pats pats  in
                      (binders1, pre, post, uu____19511)
                  | uu____19548 -> failwith "impos"))
        | uu____19582 -> failwith "Impos"  in
      match uu____19279 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19674 =
              let uu____19681 =
                let uu____19682 =
                  let uu____19689 = mk_imp pre post1  in
                  let uu____19692 =
                    let uu____19693 =
                      let uu____19714 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19714, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19693  in
                  (uu____19689, uu____19692)  in
                FStar_Syntax_Syntax.Tm_meta uu____19682  in
              FStar_Syntax_Syntax.mk uu____19681  in
            uu____19674 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19738 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19738 body
             in
          quant
  