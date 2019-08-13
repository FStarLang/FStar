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
      let uu___225_1559 = c  in
      let uu____1560 =
        let uu____1561 =
          let uu___227_1562 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___227_1562.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___227_1562.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___227_1562.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___227_1562.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1561  in
      {
        FStar_Syntax_Syntax.n = uu____1560;
        FStar_Syntax_Syntax.pos = (uu___225_1559.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___225_1559.FStar_Syntax_Syntax.vars)
      }
  
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
    | uu____1602 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1617 -> true
    | FStar_Syntax_Syntax.GTotal uu____1627 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1652  ->
               match uu___0_1652 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1656 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1673  ->
            match uu___1_1673 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1677 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1709 -> true
    | FStar_Syntax_Syntax.GTotal uu____1719 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_1734  ->
                   match uu___2_1734 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1737 -> false)))
  
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
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1778 =
      let uu____1779 = FStar_Syntax_Subst.compress t  in
      uu____1779.FStar_Syntax_Syntax.n  in
    match uu____1778 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1783,c) -> is_pure_or_ghost_comp c
    | uu____1805 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1820 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1829 =
      let uu____1830 = FStar_Syntax_Subst.compress t  in
      uu____1830.FStar_Syntax_Syntax.n  in
    match uu____1829 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1834,c) -> is_lemma_comp c
    | uu____1856 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1864 =
      let uu____1865 = FStar_Syntax_Subst.compress t  in
      uu____1865.FStar_Syntax_Syntax.n  in
    match uu____1864 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1869) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____1895) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____1932,t1,uu____1934) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1960,uu____1961) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2003) -> head_of t1
    | uu____2008 -> t
  
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
    | uu____2086 -> (t1, [])
  
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
        let uu____2168 = head_and_args' head1  in
        (match uu____2168 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____2237 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2264) ->
        FStar_Syntax_Subst.compress t2
    | uu____2269 -> t1
  
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
                (fun uu___3_2287  ->
                   match uu___3_2287 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2290 -> false)))
    | uu____2292 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2309) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2319) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2348 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2357 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___359_2369 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___359_2369.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___359_2369.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___359_2369.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___359_2369.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2385  ->
            match uu___4_2385 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2389 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2397 -> []
    | FStar_Syntax_Syntax.GTotal uu____2414 -> []
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
    | uu____2458 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2468,uu____2469) ->
        unascribe e2
    | uu____2510 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2563,uu____2564) ->
          ascribe t' k
      | uu____2605 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2632 =
      let uu____2641 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2641  in
    uu____2632 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2697 =
      let uu____2698 = FStar_Syntax_Subst.compress t  in
      uu____2698.FStar_Syntax_Syntax.n  in
    match uu____2697 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2702 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2702
    | uu____2703 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2710 =
      let uu____2711 = FStar_Syntax_Subst.compress t  in
      uu____2711.FStar_Syntax_Syntax.n  in
    match uu____2710 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2715 ->
             let uu____2724 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____2724
         | uu____2725 -> t)
    | uu____2726 -> t
  
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
      | uu____2750 -> false
  
let rec unlazy_as_t :
  'Auu____2763 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2763
  =
  fun k  ->
    fun t  ->
      let uu____2774 =
        let uu____2775 = FStar_Syntax_Subst.compress t  in
        uu____2775.FStar_Syntax_Syntax.n  in
      match uu____2774 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2780;
            FStar_Syntax_Syntax.rng = uu____2781;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____2784 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2825 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2825;
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
    let uu____2838 =
      let uu____2853 = unascribe t  in head_and_args' uu____2853  in
    match uu____2838 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2887 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2898 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2909 -> false
  
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
      | (NotEqual ,uu____2959) -> NotEqual
      | (uu____2960,NotEqual ) -> NotEqual
      | (Unknown ,uu____2961) -> Unknown
      | (uu____2962,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___5_3083 = if uu___5_3083 then Equal else Unknown  in
      let equal_iff uu___6_3094 = if uu___6_3094 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____3115 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3137 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3137
        then
          let uu____3141 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3218  ->
                    match uu____3218 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3259 = eq_tm a1 a2  in
                        eq_inj acc uu____3259) Equal) uu____3141
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3273 =
          let uu____3290 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3290 head_and_args  in
        match uu____3273 with
        | (head1,args1) ->
            let uu____3343 =
              let uu____3360 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3360 head_and_args  in
            (match uu____3343 with
             | (head2,args2) ->
                 let uu____3413 =
                   let uu____3418 =
                     let uu____3419 = un_uinst head1  in
                     uu____3419.FStar_Syntax_Syntax.n  in
                   let uu____3422 =
                     let uu____3423 = un_uinst head2  in
                     uu____3423.FStar_Syntax_Syntax.n  in
                   (uu____3418, uu____3422)  in
                 (match uu____3413 with
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
                  | uu____3450 -> FStar_Pervasives_Native.None))
         in
      let uu____3463 =
        let uu____3468 =
          let uu____3469 = unmeta t11  in uu____3469.FStar_Syntax_Syntax.n
           in
        let uu____3472 =
          let uu____3473 = unmeta t21  in uu____3473.FStar_Syntax_Syntax.n
           in
        (uu____3468, uu____3472)  in
      match uu____3463 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3479,uu____3480) ->
          let uu____3481 = unlazy t11  in eq_tm uu____3481 t21
      | (uu____3482,FStar_Syntax_Syntax.Tm_lazy uu____3483) ->
          let uu____3484 = unlazy t21  in eq_tm t11 uu____3484
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____3487 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3511 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3511
            (fun uu____3559  ->
               match uu____3559 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3574 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3574
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3588 = eq_tm f g  in
          eq_and uu____3588
            (fun uu____3591  ->
               let uu____3592 = eq_univs_list us vs  in equal_if uu____3592)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3594),uu____3595) -> Unknown
      | (uu____3596,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3597)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3600 = FStar_Const.eq_const c d  in equal_iff uu____3600
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3603)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3605))) ->
          let uu____3634 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3634
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3688 =
            let uu____3693 =
              let uu____3694 = un_uinst h1  in
              uu____3694.FStar_Syntax_Syntax.n  in
            let uu____3697 =
              let uu____3698 = un_uinst h2  in
              uu____3698.FStar_Syntax_Syntax.n  in
            (uu____3693, uu____3697)  in
          (match uu____3688 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3704 =
                    let uu____3706 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3706  in
                  FStar_List.mem uu____3704 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3708 ->
               let uu____3713 = eq_tm h1 h2  in
               eq_and uu____3713 (fun uu____3715  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3821 = FStar_List.zip bs1 bs2  in
            let uu____3884 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3921  ->
                 fun a  ->
                   match uu____3921 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4014  -> branch_matches b1 b2))
              uu____3821 uu____3884
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____4019 = eq_univs u v1  in equal_if uu____4019
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____4033 = eq_quoteinfo q1 q2  in
          eq_and uu____4033 (fun uu____4035  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____4048 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4048 (fun uu____4050  -> eq_tm phi1 phi2)
      | uu____4051 -> Unknown

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
      | ([],uu____4123) -> NotEqual
      | (uu____4154,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____4246 = eq_tm t1 t2  in
             match uu____4246 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4247 = eq_antiquotes a11 a21  in
                 (match uu____4247 with
                  | NotEqual  -> NotEqual
                  | uu____4248 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____4263) -> NotEqual
      | (uu____4270,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4300 -> NotEqual

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
        | (uu____4392,uu____4393) -> false  in
      let uu____4403 = b1  in
      match uu____4403 with
      | (p1,w1,t1) ->
          let uu____4437 = b2  in
          (match uu____4437 with
           | (p2,w2,t2) ->
               let uu____4471 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4471
               then
                 let uu____4474 =
                   (let uu____4478 = eq_tm t1 t2  in uu____4478 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4487 = eq_tm t11 t21  in
                             uu____4487 = Equal) w1 w2)
                    in
                 (if uu____4474 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4552)::a11,(b,uu____4555)::b1) ->
          let uu____4629 = eq_tm a b  in
          (match uu____4629 with
           | Equal  -> eq_args a11 b1
           | uu____4630 -> Unknown)
      | uu____4631 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4667) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4673,uu____4674) ->
        unrefine t2
    | uu____4715 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4723 =
      let uu____4724 = FStar_Syntax_Subst.compress t  in
      uu____4724.FStar_Syntax_Syntax.n  in
    match uu____4723 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4728 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4743) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4748 ->
        let uu____4765 =
          let uu____4766 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4766 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4765 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4829,uu____4830) ->
        is_uvar t1
    | uu____4871 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4880 =
      let uu____4881 = unrefine t  in uu____4881.FStar_Syntax_Syntax.n  in
    match uu____4880 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____4887) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4913) -> is_unit t1
    | uu____4918 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4927 =
      let uu____4928 = FStar_Syntax_Subst.compress t  in
      uu____4928.FStar_Syntax_Syntax.n  in
    match uu____4927 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____4933 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4942 =
      let uu____4943 = unrefine t  in uu____4943.FStar_Syntax_Syntax.n  in
    match uu____4942 with
    | FStar_Syntax_Syntax.Tm_type uu____4947 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____4951) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4977) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____4982,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____5004 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5013 =
      let uu____5014 = FStar_Syntax_Subst.compress e  in
      uu____5014.FStar_Syntax_Syntax.n  in
    match uu____5013 with
    | FStar_Syntax_Syntax.Tm_abs uu____5018 -> true
    | uu____5038 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5047 =
      let uu____5048 = FStar_Syntax_Subst.compress t  in
      uu____5048.FStar_Syntax_Syntax.n  in
    match uu____5047 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5052 -> true
    | uu____5068 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5078) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5084,uu____5085) ->
        pre_typ t2
    | uu____5126 -> t1
  
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
      let uu____5151 =
        let uu____5152 = un_uinst typ1  in uu____5152.FStar_Syntax_Syntax.n
         in
      match uu____5151 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5217 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5247 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5268,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5275) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5280,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5291,uu____5292,uu____5293,uu____5294,uu____5295) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5305,uu____5306,uu____5307,uu____5308) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5314,uu____5315,uu____5316,uu____5317,uu____5318) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5326,uu____5327) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5329,uu____5330) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5333 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5334 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5335 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5349 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5375  ->
    match uu___7_5375 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5389 'Auu____5390 .
    ('Auu____5389 FStar_Syntax_Syntax.syntax * 'Auu____5390) ->
      FStar_Range.range
  =
  fun uu____5401  ->
    match uu____5401 with | (hd1,uu____5409) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5423 'Auu____5424 .
    ('Auu____5423 FStar_Syntax_Syntax.syntax * 'Auu____5424) Prims.list ->
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
      | uu____5522 ->
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
      let uu____5581 =
        FStar_List.map
          (fun uu____5608  ->
             match uu____5608 with
             | (bv,aq) ->
                 let uu____5627 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5627, aq)) bs
         in
      mk_app f uu____5581
  
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
          let uu____5677 = FStar_Ident.range_of_lid l  in
          let uu____5678 =
            let uu____5687 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5687  in
          uu____5678 FStar_Pervasives_Native.None uu____5677
      | uu____5692 ->
          let e =
            let uu____5706 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5706 args  in
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
          let uu____5783 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5783
          then
            let uu____5786 =
              let uu____5792 =
                let uu____5794 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5794  in
              let uu____5797 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5792, uu____5797)  in
            FStar_Ident.mk_ident uu____5786
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___950_5802 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___950_5802.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___950_5802.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5803 = mk_field_projector_name_from_ident lid nm  in
        (uu____5803, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5815) -> ses
    | uu____5824 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____5835 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
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
          let uu____5870 =
            let uu___967_5871 = r  in
            let uu____5872 = f r.FStar_Syntax_Syntax.if_then_else  in
            let uu____5873 = f r.FStar_Syntax_Syntax.ite_wp  in
            let uu____5874 = f r.FStar_Syntax_Syntax.close_wp  in
            {
              FStar_Syntax_Syntax.if_then_else = uu____5872;
              FStar_Syntax_Syntax.ite_wp = uu____5873;
              FStar_Syntax_Syntax.close_wp = uu____5874
            }  in
          FStar_Util.Inl uu____5870
      | FStar_Util.Inr r ->
          let uu____5876 =
            let uu___971_5877 = r  in
            let uu____5878 = f r.FStar_Syntax_Syntax.conjunction  in
            { FStar_Syntax_Syntax.conjunction = uu____5878 }  in
          FStar_Util.Inr uu____5876
  
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
    | uu____5906 ->
        failwith
          "Impossible! get_match_with_close_wps called with a match_with_subst wp"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5929 = FStar_Syntax_Unionfind.find uv  in
      match uu____5929 with
      | FStar_Pervasives_Native.Some uu____5932 ->
          let uu____5933 =
            let uu____5935 =
              let uu____5937 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5937  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5935  in
          failwith uu____5933
      | uu____5942 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____6025 -> q1 = q2
  
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
              let uu____6071 =
                let uu___1025_6072 = rc  in
                let uu____6073 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1025_6072.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6073;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1025_6072.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6071
           in
        match bs with
        | [] -> t
        | uu____6090 ->
            let body =
              let uu____6092 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6092  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6122 =
                   let uu____6129 =
                     let uu____6130 =
                       let uu____6149 =
                         let uu____6158 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6158 bs'  in
                       let uu____6173 = close_lopt lopt'  in
                       (uu____6149, t1, uu____6173)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6130  in
                   FStar_Syntax_Syntax.mk uu____6129  in
                 uu____6122 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6188 ->
                 let uu____6189 =
                   let uu____6196 =
                     let uu____6197 =
                       let uu____6216 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6225 = close_lopt lopt  in
                       (uu____6216, body, uu____6225)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6197  in
                   FStar_Syntax_Syntax.mk uu____6196  in
                 uu____6189 FStar_Pervasives_Native.None
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
      | uu____6281 ->
          let uu____6290 =
            let uu____6297 =
              let uu____6298 =
                let uu____6313 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6322 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6313, uu____6322)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6298  in
            FStar_Syntax_Syntax.mk uu____6297  in
          uu____6290 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6371 =
        let uu____6372 = FStar_Syntax_Subst.compress t  in
        uu____6372.FStar_Syntax_Syntax.n  in
      match uu____6371 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6402) ->
               let uu____6411 =
                 let uu____6412 = FStar_Syntax_Subst.compress tres  in
                 uu____6412.FStar_Syntax_Syntax.n  in
               (match uu____6411 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6455 -> t)
           | uu____6456 -> t)
      | uu____6457 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6475 =
        let uu____6476 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6476 t.FStar_Syntax_Syntax.pos  in
      let uu____6477 =
        let uu____6484 =
          let uu____6485 =
            let uu____6492 =
              let uu____6495 =
                let uu____6496 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6496]  in
              FStar_Syntax_Subst.close uu____6495 t  in
            (b, uu____6492)  in
          FStar_Syntax_Syntax.Tm_refine uu____6485  in
        FStar_Syntax_Syntax.mk uu____6484  in
      uu____6477 FStar_Pervasives_Native.None uu____6475
  
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
        let uu____6576 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6576 with
         | (bs1,c1) ->
             let uu____6595 = is_total_comp c1  in
             if uu____6595
             then
               let uu____6610 = arrow_formals_comp (comp_result c1)  in
               (match uu____6610 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6677;
           FStar_Syntax_Syntax.index = uu____6678;
           FStar_Syntax_Syntax.sort = s;_},uu____6680)
        ->
        let rec aux s1 k2 =
          let uu____6711 =
            let uu____6712 = FStar_Syntax_Subst.compress s1  in
            uu____6712.FStar_Syntax_Syntax.n  in
          match uu____6711 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6727 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6742;
                 FStar_Syntax_Syntax.index = uu____6743;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6745)
              -> aux s2 k2
          | uu____6753 ->
              let uu____6754 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6754)
           in
        aux s k1
    | uu____6769 ->
        let uu____6770 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6770)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6805 = arrow_formals_comp k  in
    match uu____6805 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6947 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6947 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6971 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_6980  ->
                         match uu___8_6980 with
                         | FStar_Syntax_Syntax.DECREASES uu____6982 -> true
                         | uu____6986 -> false))
                  in
               (match uu____6971 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7021 ->
                    let uu____7024 = is_total_comp c1  in
                    if uu____7024
                    then
                      let uu____7043 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7043 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7136;
             FStar_Syntax_Syntax.index = uu____7137;
             FStar_Syntax_Syntax.sort = k2;_},uu____7139)
          -> arrow_until_decreases k2
      | uu____7147 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7168 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7168 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7222 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7243 =
                 FStar_Common.tabulate n_univs (fun uu____7249  -> false)  in
               let uu____7252 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7277  ->
                         match uu____7277 with
                         | (x,uu____7286) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7243 uu____7252)
           in
        ((n_univs + (FStar_List.length bs)), uu____7222)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7342 =
            let uu___1147_7343 = rc  in
            let uu____7344 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1147_7343.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7344;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1147_7343.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7342
      | uu____7353 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7387 =
        let uu____7388 =
          let uu____7391 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7391  in
        uu____7388.FStar_Syntax_Syntax.n  in
      match uu____7387 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7437 = aux t2 what  in
          (match uu____7437 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7509 -> ([], t1, abs_body_lcomp)  in
    let uu____7526 = aux t FStar_Pervasives_Native.None  in
    match uu____7526 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7574 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7574 with
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
                    | (FStar_Pervasives_Native.None ,uu____7737) -> def
                    | (uu____7748,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7760) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _7776  ->
                                  FStar_Syntax_Syntax.U_name _7776))
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
            let uu____7858 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7858 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7893 ->
            let t' = arrow binders c  in
            let uu____7905 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____7905 with
             | (uvs1,t'1) ->
                 let uu____7926 =
                   let uu____7927 = FStar_Syntax_Subst.compress t'1  in
                   uu____7927.FStar_Syntax_Syntax.n  in
                 (match uu____7926 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____7976 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____8001 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8012 -> false
  
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
      let uu____8075 =
        let uu____8076 = pre_typ t  in uu____8076.FStar_Syntax_Syntax.n  in
      match uu____8075 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8081 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8095 =
        let uu____8096 = pre_typ t  in uu____8096.FStar_Syntax_Syntax.n  in
      match uu____8095 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8100 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8102) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8128) ->
          is_constructed_typ t1 lid
      | uu____8133 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8146 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8147 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8148 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8150) -> get_tycon t2
    | uu____8175 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8183 =
      let uu____8184 = un_uinst t  in uu____8184.FStar_Syntax_Syntax.n  in
    match uu____8183 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8189 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8203 =
        let uu____8207 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8207  in
      match uu____8203 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8239 -> false
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
  fun uu____8258  ->
    let u =
      let uu____8264 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _8281  -> FStar_Syntax_Syntax.U_unif _8281)
        uu____8264
       in
    let uu____8282 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8282, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8295 = eq_tm a a'  in
      match uu____8295 with | Equal  -> true | uu____8298 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8303 =
    let uu____8310 =
      let uu____8311 =
        let uu____8312 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8312
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8311  in
    FStar_Syntax_Syntax.mk uu____8310  in
  uu____8303 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8424 =
            let uu____8427 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8428 =
              let uu____8435 =
                let uu____8436 =
                  let uu____8453 =
                    let uu____8464 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8473 =
                      let uu____8484 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8484]  in
                    uu____8464 :: uu____8473  in
                  (tand, uu____8453)  in
                FStar_Syntax_Syntax.Tm_app uu____8436  in
              FStar_Syntax_Syntax.mk uu____8435  in
            uu____8428 FStar_Pervasives_Native.None uu____8427  in
          FStar_Pervasives_Native.Some uu____8424
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8561 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8562 =
          let uu____8569 =
            let uu____8570 =
              let uu____8587 =
                let uu____8598 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8607 =
                  let uu____8618 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8618]  in
                uu____8598 :: uu____8607  in
              (op_t, uu____8587)  in
            FStar_Syntax_Syntax.Tm_app uu____8570  in
          FStar_Syntax_Syntax.mk uu____8569  in
        uu____8562 FStar_Pervasives_Native.None uu____8561
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8675 =
      let uu____8682 =
        let uu____8683 =
          let uu____8700 =
            let uu____8711 = FStar_Syntax_Syntax.as_arg phi  in [uu____8711]
             in
          (t_not, uu____8700)  in
        FStar_Syntax_Syntax.Tm_app uu____8683  in
      FStar_Syntax_Syntax.mk uu____8682  in
    uu____8675 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____8908 =
      let uu____8915 =
        let uu____8916 =
          let uu____8933 =
            let uu____8944 = FStar_Syntax_Syntax.as_arg e  in [uu____8944]
             in
          (b2t_v, uu____8933)  in
        FStar_Syntax_Syntax.Tm_app uu____8916  in
      FStar_Syntax_Syntax.mk uu____8915  in
    uu____8908 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____8991 = head_and_args e  in
    match uu____8991 with
    | (hd1,args) ->
        let uu____9036 =
          let uu____9051 =
            let uu____9052 = FStar_Syntax_Subst.compress hd1  in
            uu____9052.FStar_Syntax_Syntax.n  in
          (uu____9051, args)  in
        (match uu____9036 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9069)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9104 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9126 =
      let uu____9127 = unmeta t  in uu____9127.FStar_Syntax_Syntax.n  in
    match uu____9126 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9132 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9155 = is_t_true t1  in
      if uu____9155
      then t2
      else
        (let uu____9162 = is_t_true t2  in
         if uu____9162 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9190 = is_t_true t1  in
      if uu____9190
      then t_true
      else
        (let uu____9197 = is_t_true t2  in
         if uu____9197 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9226 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9227 =
        let uu____9234 =
          let uu____9235 =
            let uu____9252 =
              let uu____9263 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9272 =
                let uu____9283 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9283]  in
              uu____9263 :: uu____9272  in
            (teq, uu____9252)  in
          FStar_Syntax_Syntax.Tm_app uu____9235  in
        FStar_Syntax_Syntax.mk uu____9234  in
      uu____9227 FStar_Pervasives_Native.None uu____9226
  
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
          let uu____9350 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9351 =
            let uu____9358 =
              let uu____9359 =
                let uu____9376 =
                  let uu____9387 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9396 =
                    let uu____9407 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9416 =
                      let uu____9427 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9427]  in
                    uu____9407 :: uu____9416  in
                  uu____9387 :: uu____9396  in
                (eq_inst, uu____9376)  in
              FStar_Syntax_Syntax.Tm_app uu____9359  in
            FStar_Syntax_Syntax.mk uu____9358  in
          uu____9351 FStar_Pervasives_Native.None uu____9350
  
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
        let uu____9504 =
          let uu____9511 =
            let uu____9512 =
              let uu____9529 =
                let uu____9540 = FStar_Syntax_Syntax.iarg t  in
                let uu____9549 =
                  let uu____9560 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9569 =
                    let uu____9580 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9580]  in
                  uu____9560 :: uu____9569  in
                uu____9540 :: uu____9549  in
              (t_has_type1, uu____9529)  in
            FStar_Syntax_Syntax.Tm_app uu____9512  in
          FStar_Syntax_Syntax.mk uu____9511  in
        uu____9504 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9657 =
          let uu____9664 =
            let uu____9665 =
              let uu____9682 =
                let uu____9693 = FStar_Syntax_Syntax.iarg t  in
                let uu____9702 =
                  let uu____9713 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9713]  in
                uu____9693 :: uu____9702  in
              (t_with_type1, uu____9682)  in
            FStar_Syntax_Syntax.Tm_app uu____9665  in
          FStar_Syntax_Syntax.mk uu____9664  in
        uu____9657 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9760 =
    let uu____9767 =
      let uu____9768 =
        let uu____9775 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9775, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9768  in
    FStar_Syntax_Syntax.mk uu____9767  in
  uu____9760 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
  
let (mk_forall_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fa  ->
    fun x  ->
      fun body  ->
        let uu____9858 =
          let uu____9865 =
            let uu____9866 =
              let uu____9883 =
                let uu____9894 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____9903 =
                  let uu____9914 =
                    let uu____9923 =
                      let uu____9924 =
                        let uu____9925 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____9925]  in
                      abs uu____9924 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____9923  in
                  [uu____9914]  in
                uu____9894 :: uu____9903  in
              (fa, uu____9883)  in
            FStar_Syntax_Syntax.Tm_app uu____9866  in
          FStar_Syntax_Syntax.mk uu____9865  in
        uu____9858 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10052 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10052
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10071 -> true
    | uu____10073 -> false
  
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
          let uu____10120 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10120, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10149 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10149, FStar_Pervasives_Native.None, t2)  in
        let uu____10163 =
          let uu____10164 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10164  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10163
  
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
      let uu____10240 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10243 =
        let uu____10254 = FStar_Syntax_Syntax.as_arg p  in [uu____10254]  in
      mk_app uu____10240 uu____10243
  
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
      let uu____10294 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10297 =
        let uu____10308 = FStar_Syntax_Syntax.as_arg p  in [uu____10308]  in
      mk_app uu____10294 uu____10297
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10343 = head_and_args t  in
    match uu____10343 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____10392 =
          let uu____10407 =
            let uu____10408 = FStar_Syntax_Subst.compress head3  in
            uu____10408.FStar_Syntax_Syntax.n  in
          (uu____10407, args)  in
        (match uu____10392 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10427)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10493 =
                    let uu____10498 =
                      let uu____10499 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10499]  in
                    FStar_Syntax_Subst.open_term uu____10498 p  in
                  (match uu____10493 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10556 -> failwith "impossible"  in
                       let uu____10564 =
                         let uu____10566 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10566
                          in
                       if uu____10564
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10582 -> FStar_Pervasives_Native.None)
         | uu____10585 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10616 = head_and_args t  in
    match uu____10616 with
    | (head1,args) ->
        let uu____10667 =
          let uu____10682 =
            let uu____10683 = FStar_Syntax_Subst.compress head1  in
            uu____10683.FStar_Syntax_Syntax.n  in
          (uu____10682, args)  in
        (match uu____10667 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10705;
               FStar_Syntax_Syntax.vars = uu____10706;_},u::[]),(t1,uu____10709)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10756 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10791 = head_and_args t  in
    match uu____10791 with
    | (head1,args) ->
        let uu____10842 =
          let uu____10857 =
            let uu____10858 = FStar_Syntax_Subst.compress head1  in
            uu____10858.FStar_Syntax_Syntax.n  in
          (uu____10857, args)  in
        (match uu____10842 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10880;
               FStar_Syntax_Syntax.vars = uu____10881;_},u::[]),(t1,uu____10884)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10931 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____10959 =
      let uu____10976 = unmeta t  in head_and_args uu____10976  in
    match uu____10959 with
    | (head1,uu____10979) ->
        let uu____11004 =
          let uu____11005 = un_uinst head1  in
          uu____11005.FStar_Syntax_Syntax.n  in
        (match uu____11004 with
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
         | uu____11010 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11030 =
      let uu____11043 =
        let uu____11044 = FStar_Syntax_Subst.compress t  in
        uu____11044.FStar_Syntax_Syntax.n  in
      match uu____11043 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____11174 =
            let uu____11185 =
              let uu____11186 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____11186  in
            (b, uu____11185)  in
          FStar_Pervasives_Native.Some uu____11174
      | uu____11203 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____11030
      (fun uu____11241  ->
         match uu____11241 with
         | (b,c) ->
             let uu____11278 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11278 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11341 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11378 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11378
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11430 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11473 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11514 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11900) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11912) ->
          unmeta_monadic t
      | uu____11925 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____11994 =
        match uu____11994 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12032  ->
                   match uu____12032 with
                   | (lid,out_lid) ->
                       let uu____12041 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12041
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12068 = head_and_args t  in
      match uu____12068 with
      | (hd1,args) ->
          let uu____12113 =
            let uu____12114 = un_uinst hd1  in
            uu____12114.FStar_Syntax_Syntax.n  in
          (match uu____12113 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12120 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12129 = un_squash t  in
      FStar_Util.bind_opt uu____12129
        (fun t1  ->
           let uu____12145 = head_and_args' t1  in
           match uu____12145 with
           | (hd1,args) ->
               let uu____12184 =
                 let uu____12185 = un_uinst hd1  in
                 uu____12185.FStar_Syntax_Syntax.n  in
               (match uu____12184 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12191 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12232,pats)) ->
          let uu____12270 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12270)
      | uu____12283 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12350 = head_and_args t1  in
        match uu____12350 with
        | (t2,args) ->
            let uu____12405 = un_uinst t2  in
            let uu____12406 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12447  ->
                      match uu____12447 with
                      | (t3,imp) ->
                          let uu____12466 = unascribe t3  in
                          (uu____12466, imp)))
               in
            (uu____12405, uu____12406)
         in
      let rec aux qopt out t1 =
        let uu____12517 = let uu____12541 = flat t1  in (qopt, uu____12541)
           in
        match uu____12517 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12581;
                 FStar_Syntax_Syntax.vars = uu____12582;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12585);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12586;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12587;_},uu____12588)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12690;
                 FStar_Syntax_Syntax.vars = uu____12691;_},uu____12692::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12695);
                  FStar_Syntax_Syntax.pos = uu____12696;
                  FStar_Syntax_Syntax.vars = uu____12697;_},uu____12698)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12815;
               FStar_Syntax_Syntax.vars = uu____12816;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12819);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12820;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12821;_},uu____12822)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12915 =
              let uu____12919 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12919  in
            aux uu____12915 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12929;
               FStar_Syntax_Syntax.vars = uu____12930;_},uu____12931::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12934);
                FStar_Syntax_Syntax.pos = uu____12935;
                FStar_Syntax_Syntax.vars = uu____12936;_},uu____12937)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13046 =
              let uu____13050 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13050  in
            aux uu____13046 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13060) ->
            let bs = FStar_List.rev out  in
            let uu____13113 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13113 with
             | (bs1,t2) ->
                 let uu____13122 = patterns t2  in
                 (match uu____13122 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13172 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13227 = un_squash t  in
      FStar_Util.bind_opt uu____13227
        (fun t1  ->
           let uu____13242 = arrow_one t1  in
           match uu____13242 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13257 =
                 let uu____13259 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13259  in
               if uu____13257
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13269 = comp_to_comp_typ_nouniv c  in
                    uu____13269.FStar_Syntax_Syntax.result_typ  in
                  let uu____13270 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13270
                  then
                    let uu____13277 = patterns q  in
                    match uu____13277 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13340 =
                       let uu____13341 =
                         let uu____13346 =
                           let uu____13347 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13358 =
                             let uu____13369 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13369]  in
                           uu____13347 :: uu____13358  in
                         (FStar_Parser_Const.imp_lid, uu____13346)  in
                       BaseConn uu____13341  in
                     FStar_Pervasives_Native.Some uu____13340))
           | uu____13402 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13410 = un_squash t  in
      FStar_Util.bind_opt uu____13410
        (fun t1  ->
           let uu____13441 = head_and_args' t1  in
           match uu____13441 with
           | (hd1,args) ->
               let uu____13480 =
                 let uu____13495 =
                   let uu____13496 = un_uinst hd1  in
                   uu____13496.FStar_Syntax_Syntax.n  in
                 (uu____13495, args)  in
               (match uu____13480 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13513)::(a2,uu____13515)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13566 =
                      let uu____13567 = FStar_Syntax_Subst.compress a2  in
                      uu____13567.FStar_Syntax_Syntax.n  in
                    (match uu____13566 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13574) ->
                         let uu____13609 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13609 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13662 -> failwith "impossible"  in
                              let uu____13670 = patterns q1  in
                              (match uu____13670 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13731 -> FStar_Pervasives_Native.None)
                | uu____13732 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13755 = destruct_sq_forall phi  in
          (match uu____13755 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13765  -> FStar_Pervasives_Native.Some _13765)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13772 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13778 = destruct_sq_exists phi  in
          (match uu____13778 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13788  -> FStar_Pervasives_Native.Some _13788)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13795 -> f1)
      | uu____13798 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13802 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13802
      (fun uu____13807  ->
         let uu____13808 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13808
           (fun uu____13813  ->
              let uu____13814 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13814
                (fun uu____13819  ->
                   let uu____13820 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13820
                     (fun uu____13825  ->
                        let uu____13826 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13826
                          (fun uu____13830  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13848 =
            let uu____13853 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13853  in
          let uu____13854 =
            let uu____13855 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13855  in
          let uu____13858 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13848 a.FStar_Syntax_Syntax.action_univs uu____13854
            FStar_Parser_Const.effect_Tot_lid uu____13858 [] pos
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
    let uu____13884 =
      let uu____13891 =
        let uu____13892 =
          let uu____13909 =
            let uu____13920 = FStar_Syntax_Syntax.as_arg t  in [uu____13920]
             in
          (reify_1, uu____13909)  in
        FStar_Syntax_Syntax.Tm_app uu____13892  in
      FStar_Syntax_Syntax.mk uu____13891  in
    uu____13884 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____13972 =
        let uu____13979 =
          let uu____13980 =
            let uu____13981 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____13981  in
          FStar_Syntax_Syntax.Tm_constant uu____13980  in
        FStar_Syntax_Syntax.mk uu____13979  in
      uu____13972 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____13983 =
      let uu____13990 =
        let uu____13991 =
          let uu____14008 =
            let uu____14019 = FStar_Syntax_Syntax.as_arg t  in [uu____14019]
             in
          (reflect_, uu____14008)  in
        FStar_Syntax_Syntax.Tm_app uu____13991  in
      FStar_Syntax_Syntax.mk uu____13990  in
    uu____13983 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14063 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14088 = unfold_lazy i  in delta_qualifier uu____14088
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14090 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14091 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14092 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14115 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14128 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14129 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14136 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14137 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14153) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14158;
           FStar_Syntax_Syntax.index = uu____14159;
           FStar_Syntax_Syntax.sort = t2;_},uu____14161)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14170) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14176,uu____14177) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14219) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14244,t2,uu____14246) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14271,t2) -> delta_qualifier t2
  
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
    let uu____14310 = delta_qualifier t  in incr_delta_depth uu____14310
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14318 =
      let uu____14319 = FStar_Syntax_Subst.compress t  in
      uu____14319.FStar_Syntax_Syntax.n  in
    match uu____14318 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14324 -> false
  
let rec apply_last :
  'Auu____14333 .
    ('Auu____14333 -> 'Auu____14333) ->
      'Auu____14333 Prims.list -> 'Auu____14333 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14359 = f a  in [uu____14359]
      | x::xs -> let uu____14364 = apply_last f xs  in x :: uu____14364
  
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
          let uu____14419 =
            let uu____14426 =
              let uu____14427 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14427  in
            FStar_Syntax_Syntax.mk uu____14426  in
          uu____14419 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____14441 =
            let uu____14446 =
              let uu____14447 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14447
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14446 args  in
          uu____14441 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14461 =
            let uu____14466 =
              let uu____14467 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14467
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14466 args  in
          uu____14461 FStar_Pervasives_Native.None pos  in
        let uu____14468 =
          let uu____14469 =
            let uu____14470 = FStar_Syntax_Syntax.iarg typ  in [uu____14470]
             in
          nil uu____14469 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14504 =
                 let uu____14505 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14514 =
                   let uu____14525 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14534 =
                     let uu____14545 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14545]  in
                   uu____14525 :: uu____14534  in
                 uu____14505 :: uu____14514  in
               cons1 uu____14504 t.FStar_Syntax_Syntax.pos) l uu____14468
  
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
        | uu____14654 -> false
  
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
          | uu____14768 -> false
  
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
        | uu____14934 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____14972 = FStar_ST.op_Bang debug_term_eq  in
          if uu____14972
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
        let t11 = let uu____15185 = unmeta_safe t1  in canon_app uu____15185
           in
        let t21 = let uu____15191 = unmeta_safe t2  in canon_app uu____15191
           in
        let uu____15194 =
          let uu____15199 =
            let uu____15200 =
              let uu____15203 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15203  in
            uu____15200.FStar_Syntax_Syntax.n  in
          let uu____15204 =
            let uu____15205 =
              let uu____15208 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15208  in
            uu____15205.FStar_Syntax_Syntax.n  in
          (uu____15199, uu____15204)  in
        match uu____15194 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15210,uu____15211) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15220,FStar_Syntax_Syntax.Tm_uinst uu____15221) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15230,uu____15231) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15256,FStar_Syntax_Syntax.Tm_delayed uu____15257) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15282,uu____15283) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15312,FStar_Syntax_Syntax.Tm_ascribed uu____15313) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15352 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15352
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15357 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15357
        | (FStar_Syntax_Syntax.Tm_type
           uu____15360,FStar_Syntax_Syntax.Tm_type uu____15361) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15419 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15419) &&
              (let uu____15429 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15429)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15478 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15478) &&
              (let uu____15488 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15488)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15505 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15505) &&
              (let uu____15509 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15509)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15566 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15566) &&
              (let uu____15570 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15570)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15659 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15659) &&
              (let uu____15663 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15663)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15680,uu____15681) ->
            let uu____15682 =
              let uu____15684 = unlazy t11  in
              term_eq_dbg dbg uu____15684 t21  in
            check "lazy_l" uu____15682
        | (uu____15686,FStar_Syntax_Syntax.Tm_lazy uu____15687) ->
            let uu____15688 =
              let uu____15690 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15690  in
            check "lazy_r" uu____15688
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15735 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15735))
              &&
              (let uu____15739 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15739)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15743),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15745)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15803 =
               let uu____15805 = eq_quoteinfo qi1 qi2  in uu____15805 = Equal
                in
             check "tm_quoted qi" uu____15803) &&
              (let uu____15808 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15808)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15838 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15838) &&
                   (let uu____15842 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15842)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15861 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15861) &&
                    (let uu____15865 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15865))
                   &&
                   (let uu____15869 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15869)
             | uu____15872 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15878) -> fail "unk"
        | (uu____15880,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15882,uu____15883) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15885,uu____15886) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15888,uu____15889) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15891,uu____15892) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15894,uu____15895) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15897,uu____15898) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15918,uu____15919) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15935,uu____15936) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15944,uu____15945) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15963,uu____15964) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____15988,uu____15989) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16004,uu____16005) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16019,uu____16020) ->
            fail "bottom"
        | (uu____16028,FStar_Syntax_Syntax.Tm_bvar uu____16029) ->
            fail "bottom"
        | (uu____16031,FStar_Syntax_Syntax.Tm_name uu____16032) ->
            fail "bottom"
        | (uu____16034,FStar_Syntax_Syntax.Tm_fvar uu____16035) ->
            fail "bottom"
        | (uu____16037,FStar_Syntax_Syntax.Tm_constant uu____16038) ->
            fail "bottom"
        | (uu____16040,FStar_Syntax_Syntax.Tm_type uu____16041) ->
            fail "bottom"
        | (uu____16043,FStar_Syntax_Syntax.Tm_abs uu____16044) ->
            fail "bottom"
        | (uu____16064,FStar_Syntax_Syntax.Tm_arrow uu____16065) ->
            fail "bottom"
        | (uu____16081,FStar_Syntax_Syntax.Tm_refine uu____16082) ->
            fail "bottom"
        | (uu____16090,FStar_Syntax_Syntax.Tm_app uu____16091) ->
            fail "bottom"
        | (uu____16109,FStar_Syntax_Syntax.Tm_match uu____16110) ->
            fail "bottom"
        | (uu____16134,FStar_Syntax_Syntax.Tm_let uu____16135) ->
            fail "bottom"
        | (uu____16150,FStar_Syntax_Syntax.Tm_uvar uu____16151) ->
            fail "bottom"
        | (uu____16165,FStar_Syntax_Syntax.Tm_meta uu____16166) ->
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
               let uu____16201 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16201)
          (fun q1  ->
             fun q2  ->
               let uu____16213 =
                 let uu____16215 = eq_aqual q1 q2  in uu____16215 = Equal  in
               check "arg qual" uu____16213) a1 a2

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
               let uu____16240 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16240)
          (fun q1  ->
             fun q2  ->
               let uu____16252 =
                 let uu____16254 = eq_aqual q1 q2  in uu____16254 = Equal  in
               check "binder qual" uu____16252) b1 b2

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
        ((let uu____16271 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16271) &&
           (let uu____16275 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16275))
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
    fun uu____16285  ->
      fun uu____16286  ->
        match (uu____16285, uu____16286) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16413 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16413) &&
               (let uu____16417 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16417))
              &&
              (let uu____16421 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16463 -> false  in
               check "branch when" uu____16421)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16484 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16484) &&
           (let uu____16493 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16493))
          &&
          (let uu____16497 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16497)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16514 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16514 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16568 ->
        let uu____16591 =
          let uu____16593 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16593  in
        Prims.int_one + uu____16591
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16596 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16596
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16600 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16600
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16609 = sizeof t1  in (FStar_List.length us) + uu____16609
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16613) ->
        let uu____16638 = sizeof t1  in
        let uu____16640 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16655  ->
                 match uu____16655 with
                 | (bv,uu____16665) ->
                     let uu____16670 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16670) Prims.int_zero bs
           in
        uu____16638 + uu____16640
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____16699 = sizeof hd1  in
        let uu____16701 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16716  ->
                 match uu____16716 with
                 | (arg,uu____16726) ->
                     let uu____16731 = sizeof arg  in acc + uu____16731)
            Prims.int_zero args
           in
        uu____16699 + uu____16701
    | uu____16734 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16748 =
        let uu____16749 = un_uinst t  in uu____16749.FStar_Syntax_Syntax.n
         in
      match uu____16748 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16754 -> false
  
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
        let uu____16798 = FStar_Options.set_options s  in
        match uu____16798 with
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
          ((let uu____16812 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16812 (fun a1  -> ()));
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
          let uu____16827 = FStar_Options.internal_pop ()  in
          if uu____16827
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
    | FStar_Syntax_Syntax.Tm_delayed uu____16859 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____16886 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____16901 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____16902 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____16903 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16912) ->
        let uu____16937 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____16937 with
         | (bs1,t2) ->
             let uu____16946 =
               FStar_List.collect
                 (fun uu____16958  ->
                    match uu____16958 with
                    | (b,uu____16968) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____16973 = unbound_variables t2  in
             FStar_List.append uu____16946 uu____16973)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____16998 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____16998 with
         | (bs1,c1) ->
             let uu____17007 =
               FStar_List.collect
                 (fun uu____17019  ->
                    match uu____17019 with
                    | (b,uu____17029) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17034 = unbound_variables_comp c1  in
             FStar_List.append uu____17007 uu____17034)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17043 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17043 with
         | (bs,t2) ->
             let uu____17066 =
               FStar_List.collect
                 (fun uu____17078  ->
                    match uu____17078 with
                    | (b1,uu____17088) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17093 = unbound_variables t2  in
             FStar_List.append uu____17066 uu____17093)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17122 =
          FStar_List.collect
            (fun uu____17136  ->
               match uu____17136 with
               | (x,uu____17148) -> unbound_variables x) args
           in
        let uu____17157 = unbound_variables t1  in
        FStar_List.append uu____17122 uu____17157
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17198 = unbound_variables t1  in
        let uu____17201 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17216 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17216 with
                  | (p,wopt,t2) ->
                      let uu____17238 = unbound_variables t2  in
                      let uu____17241 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17238 uu____17241))
           in
        FStar_List.append uu____17198 uu____17201
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17255) ->
        let uu____17296 = unbound_variables t1  in
        let uu____17299 =
          let uu____17302 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17333 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17302 uu____17333  in
        FStar_List.append uu____17296 uu____17299
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17374 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17377 =
          let uu____17380 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17383 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17388 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17390 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17390 with
                 | (uu____17411,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17380 uu____17383  in
        FStar_List.append uu____17374 uu____17377
    | FStar_Syntax_Syntax.Tm_let ((uu____17413,lbs),t1) ->
        let uu____17433 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17433 with
         | (lbs1,t2) ->
             let uu____17448 = unbound_variables t2  in
             let uu____17451 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17458 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17461 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17458 uu____17461) lbs1
                in
             FStar_List.append uu____17448 uu____17451)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17478 = unbound_variables t1  in
        let uu____17481 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17486,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17541  ->
                      match uu____17541 with
                      | (a,uu____17553) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17562,uu____17563,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17569,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17575 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17584 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17585 -> []  in
        FStar_List.append uu____17478 uu____17481

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17592) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17602) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17612 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17615 =
          FStar_List.collect
            (fun uu____17629  ->
               match uu____17629 with
               | (a,uu____17641) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17612 uu____17615

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
            let uu____17756 = head_and_args h  in
            (match uu____17756 with
             | (head1,args) ->
                 let uu____17817 =
                   let uu____17818 = FStar_Syntax_Subst.compress head1  in
                   uu____17818.FStar_Syntax_Syntax.n  in
                 (match uu____17817 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____17871 -> aux (h :: acc) t))
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
      let uu____17895 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____17895 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2476_17937 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2476_17937.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2476_17937.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2476_17937.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2476_17937.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____17945 =
      let uu____17946 = FStar_Syntax_Subst.compress t  in
      uu____17946.FStar_Syntax_Syntax.n  in
    match uu____17945 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____17950,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____17978)::uu____17979 ->
                  let pats' = unmeta pats  in
                  let uu____18039 = head_and_args pats'  in
                  (match uu____18039 with
                   | (head1,uu____18058) ->
                       let uu____18083 =
                         let uu____18084 = un_uinst head1  in
                         uu____18084.FStar_Syntax_Syntax.n  in
                       (match uu____18083 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18089 -> false))
              | uu____18091 -> false)
         | uu____18103 -> false)
    | uu____18105 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18121 =
      let uu____18138 = unmeta e  in head_and_args uu____18138  in
    match uu____18121 with
    | (head1,args) ->
        let uu____18169 =
          let uu____18184 =
            let uu____18185 = un_uinst head1  in
            uu____18185.FStar_Syntax_Syntax.n  in
          (uu____18184, args)  in
        (match uu____18169 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18203) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18227::(hd1,uu____18229)::(tl1,uu____18231)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18298 =
               let uu____18301 =
                 let uu____18304 = list_elements tl1  in
                 FStar_Util.must uu____18304  in
               hd1 :: uu____18301  in
             FStar_Pervasives_Native.Some uu____18298
         | uu____18313 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18342 =
      let uu____18343 = FStar_Syntax_Subst.compress t  in
      uu____18343.FStar_Syntax_Syntax.n  in
    match uu____18342 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18350) ->
        let uu____18385 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18385 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18419 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18419
             then
               let uu____18426 =
                 let uu____18437 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18437]  in
               mk_app t uu____18426
             else e1)
    | uu____18464 ->
        let uu____18465 =
          let uu____18476 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18476]  in
        mk_app t uu____18465
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18531 = list_elements e  in
        match uu____18531 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18562 =
          let uu____18579 = unmeta p  in
          FStar_All.pipe_right uu____18579 head_and_args  in
        match uu____18562 with
        | (head1,args) ->
            let uu____18630 =
              let uu____18645 =
                let uu____18646 = un_uinst head1  in
                uu____18646.FStar_Syntax_Syntax.n  in
              (uu____18645, args)  in
            (match uu____18630 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18668,uu____18669)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18721 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____18776 =
            let uu____18793 = unmeta t1  in
            FStar_All.pipe_right uu____18793 head_and_args  in
          match uu____18776 with
          | (head1,args) ->
              let uu____18840 =
                let uu____18855 =
                  let uu____18856 = un_uinst head1  in
                  uu____18856.FStar_Syntax_Syntax.n  in
                (uu____18855, args)  in
              (match uu____18840 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____18875)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____18912 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____18942 = smt_pat_or1 t1  in
            (match uu____18942 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____18964 = list_elements1 e  in
                 FStar_All.pipe_right uu____18964
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____18994 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____18994
                           (FStar_List.map one_pat)))
             | uu____19017 ->
                 let uu____19022 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19022])
        | uu____19073 ->
            let uu____19076 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19076]
         in
      let uu____19127 =
        let uu____19160 =
          let uu____19161 = FStar_Syntax_Subst.compress t  in
          uu____19161.FStar_Syntax_Syntax.n  in
        match uu____19160 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19218 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19218 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19289;
                        FStar_Syntax_Syntax.effect_name = uu____19290;
                        FStar_Syntax_Syntax.result_typ = uu____19291;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19293)::(post,uu____19295)::(pats,uu____19297)::[];
                        FStar_Syntax_Syntax.flags = uu____19298;_}
                      ->
                      let uu____19359 = lemma_pats pats  in
                      (binders1, pre, post, uu____19359)
                  | uu____19396 -> failwith "impos"))
        | uu____19430 -> failwith "Impos"  in
      match uu____19127 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19522 =
              let uu____19529 =
                let uu____19530 =
                  let uu____19537 = mk_imp pre post1  in
                  let uu____19540 =
                    let uu____19541 =
                      let uu____19562 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19562, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19541  in
                  (uu____19537, uu____19540)  in
                FStar_Syntax_Syntax.Tm_meta uu____19530  in
              FStar_Syntax_Syntax.mk uu____19529  in
            uu____19522 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19586 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19586 body
             in
          quant
  