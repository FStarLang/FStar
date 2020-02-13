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
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1624)::[] -> wp
      | uu____1649 ->
          let uu____1660 =
            let uu____1662 =
              let uu____1664 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length
                 in
              FStar_All.pipe_right uu____1664 FStar_Util.string_of_int  in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____1662
             in
          failwith uu____1660
       in
    let uu____1688 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1688, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1702 -> true
    | FStar_Syntax_Syntax.GTotal uu____1712 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1737  ->
               match uu___0_1737 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1741 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1758  ->
            match uu___1_1758 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1762 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1794 -> true
    | FStar_Syntax_Syntax.GTotal uu____1804 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_1819  ->
                   match uu___2_1819 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1822 -> false)))
  
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
    let uu____1863 =
      let uu____1864 = FStar_Syntax_Subst.compress t  in
      uu____1864.FStar_Syntax_Syntax.n  in
    match uu____1863 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1868,c) -> is_pure_or_ghost_comp c
    | uu____1890 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1905 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1914 =
      let uu____1915 = FStar_Syntax_Subst.compress t  in
      uu____1915.FStar_Syntax_Syntax.n  in
    match uu____1914 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1919,c) -> is_lemma_comp c
    | uu____1941 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1949 =
      let uu____1950 = FStar_Syntax_Subst.compress t  in
      uu____1950.FStar_Syntax_Syntax.n  in
    match uu____1949 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1954) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____1980) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2017,t1,uu____2019) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2045,uu____2046) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2088) -> head_of t1
    | uu____2093 -> t
  
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
    | uu____2171 -> (t1, [])
  
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
        let uu____2253 = head_and_args' head1  in
        (match uu____2253 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____2322 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2349) ->
        FStar_Syntax_Subst.compress t2
    | uu____2354 -> t1
  
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
                (fun uu___3_2372  ->
                   match uu___3_2372 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2375 -> false)))
    | uu____2377 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2394) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2404) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2433 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2442 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___366_2454 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___366_2454.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___366_2454.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___366_2454.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___366_2454.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2470  ->
            match uu___4_2470 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2474 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2482 -> []
    | FStar_Syntax_Syntax.GTotal uu____2499 -> []
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
    | uu____2543 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2553,uu____2554) ->
        unascribe e2
    | uu____2595 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2648,uu____2649) ->
          ascribe t' k
      | uu____2690 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2717 =
      let uu____2726 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2726  in
    uu____2717 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2782 =
      let uu____2783 = FStar_Syntax_Subst.compress t  in
      uu____2783.FStar_Syntax_Syntax.n  in
    match uu____2782 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2787 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2787
    | uu____2788 -> t
  
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2795 =
      let uu____2796 = FStar_Syntax_Subst.compress t  in
      uu____2796.FStar_Syntax_Syntax.n  in
    match uu____2795 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2800 ->
             let uu____2809 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____2809
         | uu____2810 -> t)
    | uu____2811 -> t
  
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
      | (FStar_Syntax_Syntax.Lazy_optionstate
         ,FStar_Syntax_Syntax.Lazy_optionstate ) -> true
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
      | uu____2836 -> false
  
let unlazy_as_t :
  'Auu____2849 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2849
  =
  fun k  ->
    fun t  ->
      let uu____2860 =
        let uu____2861 = FStar_Syntax_Subst.compress t  in
        uu____2861.FStar_Syntax_Syntax.n  in
      match uu____2860 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2866;
            FStar_Syntax_Syntax.rng = uu____2867;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____2870 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2911 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2911;
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
    let uu____2924 =
      let uu____2939 = unascribe t  in head_and_args' uu____2939  in
    match uu____2924 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2973 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2984 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2995 -> false
  
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
      | (NotEqual ,uu____3045) -> NotEqual
      | (uu____3046,NotEqual ) -> NotEqual
      | (Unknown ,uu____3047) -> Unknown
      | (uu____3048,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___5_3157 = if uu___5_3157 then Equal else Unknown  in
      let equal_iff uu___6_3168 = if uu___6_3168 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____3189 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3211 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3211
        then
          let uu____3215 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3292  ->
                    match uu____3292 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3333 = eq_tm a1 a2  in
                        eq_inj acc uu____3333) Equal) uu____3215
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3347 =
          let uu____3364 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3364 head_and_args  in
        match uu____3347 with
        | (head1,args1) ->
            let uu____3417 =
              let uu____3434 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3434 head_and_args  in
            (match uu____3417 with
             | (head2,args2) ->
                 let uu____3487 =
                   let uu____3492 =
                     let uu____3493 = un_uinst head1  in
                     uu____3493.FStar_Syntax_Syntax.n  in
                   let uu____3496 =
                     let uu____3497 = un_uinst head2  in
                     uu____3497.FStar_Syntax_Syntax.n  in
                   (uu____3492, uu____3496)  in
                 (match uu____3487 with
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
                  | uu____3524 -> FStar_Pervasives_Native.None))
         in
      let uu____3537 =
        let uu____3542 =
          let uu____3543 = unmeta t11  in uu____3543.FStar_Syntax_Syntax.n
           in
        let uu____3546 =
          let uu____3547 = unmeta t21  in uu____3547.FStar_Syntax_Syntax.n
           in
        (uu____3542, uu____3546)  in
      match uu____3537 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3553,uu____3554) ->
          let uu____3555 = unlazy t11  in eq_tm uu____3555 t21
      | (uu____3556,FStar_Syntax_Syntax.Tm_lazy uu____3557) ->
          let uu____3558 = unlazy t21  in eq_tm t11 uu____3558
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____3561 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3585 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3585
            (fun uu____3633  ->
               match uu____3633 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3648 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3648
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3662 = eq_tm f g  in
          eq_and uu____3662
            (fun uu____3665  ->
               let uu____3666 = eq_univs_list us vs  in equal_if uu____3666)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3668),uu____3669) -> Unknown
      | (uu____3670,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3671)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3674 = FStar_Const.eq_const c d  in equal_iff uu____3674
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3677)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3679))) ->
          let uu____3708 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3708
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3762 =
            let uu____3767 =
              let uu____3768 = un_uinst h1  in
              uu____3768.FStar_Syntax_Syntax.n  in
            let uu____3771 =
              let uu____3772 = un_uinst h2  in
              uu____3772.FStar_Syntax_Syntax.n  in
            (uu____3767, uu____3771)  in
          (match uu____3762 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3778 =
                    let uu____3780 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3780  in
                  FStar_List.mem uu____3778 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3782 ->
               let uu____3787 = eq_tm h1 h2  in
               eq_and uu____3787 (fun uu____3789  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3895 = FStar_List.zip bs1 bs2  in
            let uu____3958 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____3995  ->
                 fun a  ->
                   match uu____3995 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4088  -> branch_matches b1 b2))
              uu____3895 uu____3958
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____4093 = eq_univs u v1  in equal_if uu____4093
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____4107 = eq_quoteinfo q1 q2  in
          eq_and uu____4107 (fun uu____4109  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____4122 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4122 (fun uu____4124  -> eq_tm phi1 phi2)
      | uu____4125 -> Unknown

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
      | ([],uu____4197) -> NotEqual
      | (uu____4228,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____4320 = eq_tm t1 t2  in
             match uu____4320 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4321 = eq_antiquotes a11 a21  in
                 (match uu____4321 with
                  | NotEqual  -> NotEqual
                  | uu____4322 -> Unknown)
             | Equal  -> eq_antiquotes a11 a21)

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
        | (uu____4406,uu____4407) -> false  in
      let uu____4417 = b1  in
      match uu____4417 with
      | (p1,w1,t1) ->
          let uu____4451 = b2  in
          (match uu____4451 with
           | (p2,w2,t2) ->
               let uu____4485 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4485
               then
                 let uu____4488 =
                   (let uu____4492 = eq_tm t1 t2  in uu____4492 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4501 = eq_tm t11 t21  in
                             uu____4501 = Equal) w1 w2)
                    in
                 (if uu____4488 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4566)::a11,(b,uu____4569)::b1) ->
          let uu____4643 = eq_tm a b  in
          (match uu____4643 with
           | Equal  -> eq_args a11 b1
           | uu____4644 -> Unknown)
      | uu____4645 -> Unknown

and (eq_univs_list :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool)
  =
  fun us  ->
    fun vs  ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)

let (eq_aqual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      eq_result)
  =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          Equal
      | (FStar_Pervasives_Native.None ,uu____4700) -> NotEqual
      | (uu____4707,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4737 -> NotEqual
  
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4754) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4760,uu____4761) ->
        unrefine t2
    | uu____4802 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4810 =
      let uu____4811 = FStar_Syntax_Subst.compress t  in
      uu____4811.FStar_Syntax_Syntax.n  in
    match uu____4810 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4815 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4830) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4835 ->
        let uu____4852 =
          let uu____4853 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4853 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4852 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4916,uu____4917) ->
        is_uvar t1
    | uu____4958 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4967 =
      let uu____4968 = unrefine t  in uu____4968.FStar_Syntax_Syntax.n  in
    match uu____4967 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____4974) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5000) -> is_unit t1
    | uu____5005 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5014 =
      let uu____5015 = FStar_Syntax_Subst.compress t  in
      uu____5015.FStar_Syntax_Syntax.n  in
    match uu____5014 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5020 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5029 =
      let uu____5030 = FStar_Syntax_Subst.compress e  in
      uu____5030.FStar_Syntax_Syntax.n  in
    match uu____5029 with
    | FStar_Syntax_Syntax.Tm_abs uu____5034 -> true
    | uu____5054 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5063 =
      let uu____5064 = FStar_Syntax_Subst.compress t  in
      uu____5064.FStar_Syntax_Syntax.n  in
    match uu____5063 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5068 -> true
    | uu____5084 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5094) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5100,uu____5101) ->
        pre_typ t2
    | uu____5142 -> t1
  
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
      let uu____5167 =
        let uu____5168 = un_uinst typ1  in uu____5168.FStar_Syntax_Syntax.n
         in
      match uu____5167 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5233 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5263 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5284,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5291) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5296,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5307,uu____5308,uu____5309,uu____5310,uu____5311) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5321,uu____5322,uu____5323,uu____5324) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5330,uu____5331,uu____5332,uu____5333,uu____5334) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5342,uu____5343) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5345,uu____5346) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5348 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5349 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5350 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5351 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5375 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5401  ->
    match uu___7_5401 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5415 'Auu____5416 .
    ('Auu____5415 FStar_Syntax_Syntax.syntax * 'Auu____5416) ->
      FStar_Range.range
  =
  fun uu____5427  ->
    match uu____5427 with | (hd1,uu____5435) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5449 'Auu____5450 .
    ('Auu____5449 FStar_Syntax_Syntax.syntax * 'Auu____5450) Prims.list ->
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
      | uu____5548 ->
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
      let uu____5607 =
        FStar_List.map
          (fun uu____5634  ->
             match uu____5634 with
             | (bv,aq) ->
                 let uu____5653 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5653, aq)) bs
         in
      mk_app f uu____5607
  
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
          let uu____5703 = FStar_Ident.range_of_lid l  in
          let uu____5704 =
            let uu____5713 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5713  in
          uu____5704 FStar_Pervasives_Native.None uu____5703
      | uu____5718 ->
          let e =
            let uu____5732 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5732 args  in
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
          let uu____5809 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5809
          then
            let uu____5812 =
              let uu____5818 =
                let uu____5820 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5820  in
              let uu____5823 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5818, uu____5823)  in
            FStar_Ident.mk_ident uu____5812
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___943_5828 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___943_5828.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___943_5828.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5829 = mk_field_projector_name_from_ident lid nm  in
        (uu____5829, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5841) -> ses
    | uu____5850 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5865 = FStar_Syntax_Unionfind.find uv  in
      match uu____5865 with
      | FStar_Pervasives_Native.Some uu____5868 ->
          let uu____5869 =
            let uu____5871 =
              let uu____5873 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5873  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5871  in
          failwith uu____5869
      | uu____5878 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____5961 -> q1 = q2
  
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
              let uu____6007 =
                let uu___1000_6008 = rc  in
                let uu____6009 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1000_6008.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6009;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1000_6008.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6007
           in
        match bs with
        | [] -> t
        | uu____6026 ->
            let body =
              let uu____6028 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6028  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6058 =
                   let uu____6065 =
                     let uu____6066 =
                       let uu____6085 =
                         let uu____6094 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6094 bs'  in
                       let uu____6109 = close_lopt lopt'  in
                       (uu____6085, t1, uu____6109)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6066  in
                   FStar_Syntax_Syntax.mk uu____6065  in
                 uu____6058 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6124 ->
                 let uu____6125 =
                   let uu____6132 =
                     let uu____6133 =
                       let uu____6152 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6161 = close_lopt lopt  in
                       (uu____6152, body, uu____6161)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6133  in
                   FStar_Syntax_Syntax.mk uu____6132  in
                 uu____6125 FStar_Pervasives_Native.None
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
      | uu____6217 ->
          let uu____6226 =
            let uu____6233 =
              let uu____6234 =
                let uu____6249 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6258 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6249, uu____6258)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6234  in
            FStar_Syntax_Syntax.mk uu____6233  in
          uu____6226 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6307 =
        let uu____6308 = FStar_Syntax_Subst.compress t  in
        uu____6308.FStar_Syntax_Syntax.n  in
      match uu____6307 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6338) ->
               let uu____6347 =
                 let uu____6348 = FStar_Syntax_Subst.compress tres  in
                 uu____6348.FStar_Syntax_Syntax.n  in
               (match uu____6347 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6391 -> t)
           | uu____6392 -> t)
      | uu____6393 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6411 =
        let uu____6412 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6412 t.FStar_Syntax_Syntax.pos  in
      let uu____6413 =
        let uu____6420 =
          let uu____6421 =
            let uu____6428 =
              let uu____6431 =
                let uu____6432 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6432]  in
              FStar_Syntax_Subst.close uu____6431 t  in
            (b, uu____6428)  in
          FStar_Syntax_Syntax.Tm_refine uu____6421  in
        FStar_Syntax_Syntax.mk uu____6420  in
      uu____6413 FStar_Pervasives_Native.None uu____6411
  
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
        let uu____6512 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6512 with
         | (bs1,c1) ->
             let uu____6531 = is_total_comp c1  in
             if uu____6531
             then
               let uu____6546 = arrow_formals_comp (comp_result c1)  in
               (match uu____6546 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6613;
           FStar_Syntax_Syntax.index = uu____6614;
           FStar_Syntax_Syntax.sort = s;_},uu____6616)
        ->
        let rec aux s1 k2 =
          let uu____6647 =
            let uu____6648 = FStar_Syntax_Subst.compress s1  in
            uu____6648.FStar_Syntax_Syntax.n  in
          match uu____6647 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6663 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6678;
                 FStar_Syntax_Syntax.index = uu____6679;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6681)
              -> aux s2 k2
          | uu____6689 ->
              let uu____6690 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6690)
           in
        aux s k1
    | uu____6705 ->
        let uu____6706 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6706)
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6741 = arrow_formals_comp k  in
    match uu____6741 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6883 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6883 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6907 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_6916  ->
                         match uu___8_6916 with
                         | FStar_Syntax_Syntax.DECREASES uu____6918 -> true
                         | uu____6922 -> false))
                  in
               (match uu____6907 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____6957 ->
                    let uu____6960 = is_total_comp c1  in
                    if uu____6960
                    then
                      let uu____6979 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____6979 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7072;
             FStar_Syntax_Syntax.index = uu____7073;
             FStar_Syntax_Syntax.sort = k2;_},uu____7075)
          -> arrow_until_decreases k2
      | uu____7083 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7104 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7104 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7158 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7179 =
                 FStar_Common.tabulate n_univs (fun uu____7185  -> false)  in
               let uu____7188 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7213  ->
                         match uu____7213 with
                         | (x,uu____7222) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7179 uu____7188)
           in
        ((n_univs + (FStar_List.length bs)), uu____7158)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7278 =
            let uu___1122_7279 = rc  in
            let uu____7280 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1122_7279.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7280;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1122_7279.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7278
      | uu____7289 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7323 =
        let uu____7324 =
          let uu____7327 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7327  in
        uu____7324.FStar_Syntax_Syntax.n  in
      match uu____7323 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7373 = aux t2 what  in
          (match uu____7373 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7445 -> ([], t1, abs_body_lcomp)  in
    let uu____7462 = aux t FStar_Pervasives_Native.None  in
    match uu____7462 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7510 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7510 with
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
                    | (FStar_Pervasives_Native.None ,uu____7673) -> def
                    | (uu____7684,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7696) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _7712  ->
                                  FStar_Syntax_Syntax.U_name _7712))
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
            let uu____7794 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7794 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7829 ->
            let t' = arrow binders c  in
            let uu____7841 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____7841 with
             | (uvs1,t'1) ->
                 let uu____7862 =
                   let uu____7863 = FStar_Syntax_Subst.compress t'1  in
                   uu____7863.FStar_Syntax_Syntax.n  in
                 (match uu____7862 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____7912 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____7937 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____7948 -> false
  
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
      let uu____8011 =
        let uu____8012 = pre_typ t  in uu____8012.FStar_Syntax_Syntax.n  in
      match uu____8011 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8017 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8031 =
        let uu____8032 = pre_typ t  in uu____8032.FStar_Syntax_Syntax.n  in
      match uu____8031 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8036 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8038) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8064) ->
          is_constructed_typ t1 lid
      | uu____8069 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8082 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8083 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8084 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8086) -> get_tycon t2
    | uu____8111 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8119 =
      let uu____8120 = un_uinst t  in uu____8120.FStar_Syntax_Syntax.n  in
    match uu____8119 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8125 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8139 =
        let uu____8143 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8143  in
      match uu____8139 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8175 -> false
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
  fun uu____8194  ->
    let u =
      let uu____8200 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _8217  -> FStar_Syntax_Syntax.U_unif _8217)
        uu____8200
       in
    let uu____8218 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8218, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8231 = eq_tm a a'  in
      match uu____8231 with | Equal  -> true | uu____8234 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8239 =
    let uu____8246 =
      let uu____8247 =
        let uu____8248 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8248
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8247  in
    FStar_Syntax_Syntax.mk uu____8246  in
  uu____8239 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8360 =
            let uu____8363 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8364 =
              let uu____8371 =
                let uu____8372 =
                  let uu____8389 =
                    let uu____8400 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8409 =
                      let uu____8420 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8420]  in
                    uu____8400 :: uu____8409  in
                  (tand, uu____8389)  in
                FStar_Syntax_Syntax.Tm_app uu____8372  in
              FStar_Syntax_Syntax.mk uu____8371  in
            uu____8364 FStar_Pervasives_Native.None uu____8363  in
          FStar_Pervasives_Native.Some uu____8360
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8497 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8498 =
          let uu____8505 =
            let uu____8506 =
              let uu____8523 =
                let uu____8534 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8543 =
                  let uu____8554 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8554]  in
                uu____8534 :: uu____8543  in
              (op_t, uu____8523)  in
            FStar_Syntax_Syntax.Tm_app uu____8506  in
          FStar_Syntax_Syntax.mk uu____8505  in
        uu____8498 FStar_Pervasives_Native.None uu____8497
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8611 =
      let uu____8618 =
        let uu____8619 =
          let uu____8636 =
            let uu____8647 = FStar_Syntax_Syntax.as_arg phi  in [uu____8647]
             in
          (t_not, uu____8636)  in
        FStar_Syntax_Syntax.Tm_app uu____8619  in
      FStar_Syntax_Syntax.mk uu____8618  in
    uu____8611 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____8844 =
      let uu____8851 =
        let uu____8852 =
          let uu____8869 =
            let uu____8880 = FStar_Syntax_Syntax.as_arg e  in [uu____8880]
             in
          (b2t_v, uu____8869)  in
        FStar_Syntax_Syntax.Tm_app uu____8852  in
      FStar_Syntax_Syntax.mk uu____8851  in
    uu____8844 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____8927 = head_and_args e  in
    match uu____8927 with
    | (hd1,args) ->
        let uu____8972 =
          let uu____8987 =
            let uu____8988 = FStar_Syntax_Subst.compress hd1  in
            uu____8988.FStar_Syntax_Syntax.n  in
          (uu____8987, args)  in
        (match uu____8972 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9005)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9040 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9062 =
      let uu____9063 = unmeta t  in uu____9063.FStar_Syntax_Syntax.n  in
    match uu____9062 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9068 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9091 = is_t_true t1  in
      if uu____9091
      then t2
      else
        (let uu____9098 = is_t_true t2  in
         if uu____9098 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9126 = is_t_true t1  in
      if uu____9126
      then t_true
      else
        (let uu____9133 = is_t_true t2  in
         if uu____9133 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9162 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9163 =
        let uu____9170 =
          let uu____9171 =
            let uu____9188 =
              let uu____9199 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9208 =
                let uu____9219 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9219]  in
              uu____9199 :: uu____9208  in
            (teq, uu____9188)  in
          FStar_Syntax_Syntax.Tm_app uu____9171  in
        FStar_Syntax_Syntax.mk uu____9170  in
      uu____9163 FStar_Pervasives_Native.None uu____9162
  
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
          let uu____9286 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9287 =
            let uu____9294 =
              let uu____9295 =
                let uu____9312 =
                  let uu____9323 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9332 =
                    let uu____9343 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9352 =
                      let uu____9363 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9363]  in
                    uu____9343 :: uu____9352  in
                  uu____9323 :: uu____9332  in
                (eq_inst, uu____9312)  in
              FStar_Syntax_Syntax.Tm_app uu____9295  in
            FStar_Syntax_Syntax.mk uu____9294  in
          uu____9287 FStar_Pervasives_Native.None uu____9286
  
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
        let uu____9440 =
          let uu____9447 =
            let uu____9448 =
              let uu____9465 =
                let uu____9476 = FStar_Syntax_Syntax.iarg t  in
                let uu____9485 =
                  let uu____9496 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9505 =
                    let uu____9516 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9516]  in
                  uu____9496 :: uu____9505  in
                uu____9476 :: uu____9485  in
              (t_has_type1, uu____9465)  in
            FStar_Syntax_Syntax.Tm_app uu____9448  in
          FStar_Syntax_Syntax.mk uu____9447  in
        uu____9440 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9593 =
          let uu____9600 =
            let uu____9601 =
              let uu____9618 =
                let uu____9629 = FStar_Syntax_Syntax.iarg t  in
                let uu____9638 =
                  let uu____9649 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9649]  in
                uu____9629 :: uu____9638  in
              (t_with_type1, uu____9618)  in
            FStar_Syntax_Syntax.Tm_app uu____9601  in
          FStar_Syntax_Syntax.mk uu____9600  in
        uu____9593 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9696 =
    let uu____9703 =
      let uu____9704 =
        let uu____9711 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9711, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9704  in
    FStar_Syntax_Syntax.mk uu____9703  in
  uu____9696 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
        let uu____9794 =
          let uu____9801 =
            let uu____9802 =
              let uu____9819 =
                let uu____9830 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____9839 =
                  let uu____9850 =
                    let uu____9859 =
                      let uu____9860 =
                        let uu____9861 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____9861]  in
                      abs uu____9860 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____9859  in
                  [uu____9850]  in
                uu____9830 :: uu____9839  in
              (fa, uu____9819)  in
            FStar_Syntax_Syntax.Tm_app uu____9802  in
          FStar_Syntax_Syntax.mk uu____9801  in
        uu____9794 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____9988 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____9988
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10007 -> true
    | uu____10009 -> false
  
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
          let uu____10056 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10056, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10085 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10085, FStar_Pervasives_Native.None, t2)  in
        let uu____10099 =
          let uu____10100 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10100  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10099
  
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
      let uu____10176 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10179 =
        let uu____10190 = FStar_Syntax_Syntax.as_arg p  in [uu____10190]  in
      mk_app uu____10176 uu____10179
  
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
      let uu____10230 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10233 =
        let uu____10244 = FStar_Syntax_Syntax.as_arg p  in [uu____10244]  in
      mk_app uu____10230 uu____10233
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10279 = head_and_args t  in
    match uu____10279 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____10328 =
          let uu____10343 =
            let uu____10344 = FStar_Syntax_Subst.compress head3  in
            uu____10344.FStar_Syntax_Syntax.n  in
          (uu____10343, args)  in
        (match uu____10328 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10363)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10429 =
                    let uu____10434 =
                      let uu____10435 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10435]  in
                    FStar_Syntax_Subst.open_term uu____10434 p  in
                  (match uu____10429 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10492 -> failwith "impossible"  in
                       let uu____10500 =
                         let uu____10502 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10502
                          in
                       if uu____10500
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10518 -> FStar_Pervasives_Native.None)
         | uu____10521 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10552 = head_and_args t  in
    match uu____10552 with
    | (head1,args) ->
        let uu____10603 =
          let uu____10618 =
            let uu____10619 = FStar_Syntax_Subst.compress head1  in
            uu____10619.FStar_Syntax_Syntax.n  in
          (uu____10618, args)  in
        (match uu____10603 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10641;
               FStar_Syntax_Syntax.vars = uu____10642;_},u::[]),(t1,uu____10645)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10692 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10727 = head_and_args t  in
    match uu____10727 with
    | (head1,args) ->
        let uu____10778 =
          let uu____10793 =
            let uu____10794 = FStar_Syntax_Subst.compress head1  in
            uu____10794.FStar_Syntax_Syntax.n  in
          (uu____10793, args)  in
        (match uu____10778 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10816;
               FStar_Syntax_Syntax.vars = uu____10817;_},u::[]),(t1,uu____10820)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10867 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____10895 =
      let uu____10912 = unmeta t  in head_and_args uu____10912  in
    match uu____10895 with
    | (head1,uu____10915) ->
        let uu____10940 =
          let uu____10941 = un_uinst head1  in
          uu____10941.FStar_Syntax_Syntax.n  in
        (match uu____10940 with
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
         | uu____10946 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10966 =
      let uu____10967 = FStar_Syntax_Subst.compress t  in
      uu____10967.FStar_Syntax_Syntax.n  in
    match uu____10966 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11073 =
          let uu____11078 =
            let uu____11079 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11079  in
          (b, uu____11078)  in
        FStar_Pervasives_Native.Some uu____11073
    | uu____11084 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11107 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11107
      (fun uu____11135  ->
         match uu____11135 with
         | (b,c) ->
             let uu____11154 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11154 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11217 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11254 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11254
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11306 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11349 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11390 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11776) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11788) ->
          unmeta_monadic t
      | uu____11801 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____11870 =
        match uu____11870 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____11908  ->
                   match uu____11908 with
                   | (lid,out_lid) ->
                       let uu____11917 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____11917
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____11944 = head_and_args t  in
      match uu____11944 with
      | (hd1,args) ->
          let uu____11989 =
            let uu____11990 = un_uinst hd1  in
            uu____11990.FStar_Syntax_Syntax.n  in
          (match uu____11989 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____11996 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12005 = un_squash t  in
      FStar_Util.bind_opt uu____12005
        (fun t1  ->
           let uu____12021 = head_and_args' t1  in
           match uu____12021 with
           | (hd1,args) ->
               let uu____12060 =
                 let uu____12061 = un_uinst hd1  in
                 uu____12061.FStar_Syntax_Syntax.n  in
               (match uu____12060 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12067 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12108,pats)) ->
          let uu____12146 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12146)
      | uu____12159 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12226 = head_and_args t1  in
        match uu____12226 with
        | (t2,args) ->
            let uu____12281 = un_uinst t2  in
            let uu____12282 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12323  ->
                      match uu____12323 with
                      | (t3,imp) ->
                          let uu____12342 = unascribe t3  in
                          (uu____12342, imp)))
               in
            (uu____12281, uu____12282)
         in
      let rec aux qopt out t1 =
        let uu____12393 = let uu____12417 = flat t1  in (qopt, uu____12417)
           in
        match uu____12393 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12457;
                 FStar_Syntax_Syntax.vars = uu____12458;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12461);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12462;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12463;_},uu____12464)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12566;
                 FStar_Syntax_Syntax.vars = uu____12567;_},uu____12568::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12571);
                  FStar_Syntax_Syntax.pos = uu____12572;
                  FStar_Syntax_Syntax.vars = uu____12573;_},uu____12574)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12691;
               FStar_Syntax_Syntax.vars = uu____12692;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12695);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12696;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12697;_},uu____12698)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12791 =
              let uu____12795 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12795  in
            aux uu____12791 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12805;
               FStar_Syntax_Syntax.vars = uu____12806;_},uu____12807::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12810);
                FStar_Syntax_Syntax.pos = uu____12811;
                FStar_Syntax_Syntax.vars = uu____12812;_},uu____12813)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12922 =
              let uu____12926 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12926  in
            aux uu____12922 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____12936) ->
            let bs = FStar_List.rev out  in
            let uu____12989 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____12989 with
             | (bs1,t2) ->
                 let uu____12998 = patterns t2  in
                 (match uu____12998 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13048 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13103 = un_squash t  in
      FStar_Util.bind_opt uu____13103
        (fun t1  ->
           let uu____13118 = arrow_one t1  in
           match uu____13118 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13133 =
                 let uu____13135 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13135  in
               if uu____13133
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13145 = comp_to_comp_typ_nouniv c  in
                    uu____13145.FStar_Syntax_Syntax.result_typ  in
                  let uu____13146 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13146
                  then
                    let uu____13153 = patterns q  in
                    match uu____13153 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13216 =
                       let uu____13217 =
                         let uu____13222 =
                           let uu____13223 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13234 =
                             let uu____13245 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13245]  in
                           uu____13223 :: uu____13234  in
                         (FStar_Parser_Const.imp_lid, uu____13222)  in
                       BaseConn uu____13217  in
                     FStar_Pervasives_Native.Some uu____13216))
           | uu____13278 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13286 = un_squash t  in
      FStar_Util.bind_opt uu____13286
        (fun t1  ->
           let uu____13317 = head_and_args' t1  in
           match uu____13317 with
           | (hd1,args) ->
               let uu____13356 =
                 let uu____13371 =
                   let uu____13372 = un_uinst hd1  in
                   uu____13372.FStar_Syntax_Syntax.n  in
                 (uu____13371, args)  in
               (match uu____13356 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13389)::(a2,uu____13391)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13442 =
                      let uu____13443 = FStar_Syntax_Subst.compress a2  in
                      uu____13443.FStar_Syntax_Syntax.n  in
                    (match uu____13442 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13450) ->
                         let uu____13485 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13485 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13538 -> failwith "impossible"  in
                              let uu____13546 = patterns q1  in
                              (match uu____13546 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13607 -> FStar_Pervasives_Native.None)
                | uu____13608 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13631 = destruct_sq_forall phi  in
          (match uu____13631 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13641  -> FStar_Pervasives_Native.Some _13641)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13648 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13654 = destruct_sq_exists phi  in
          (match uu____13654 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13664  -> FStar_Pervasives_Native.Some _13664)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13671 -> f1)
      | uu____13674 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13678 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13678
      (fun uu____13683  ->
         let uu____13684 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13684
           (fun uu____13689  ->
              let uu____13690 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13690
                (fun uu____13695  ->
                   let uu____13696 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13696
                     (fun uu____13701  ->
                        let uu____13702 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13702
                          (fun uu____13706  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13724 =
            let uu____13729 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13729  in
          let uu____13730 =
            let uu____13731 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13731  in
          let uu____13734 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13724 a.FStar_Syntax_Syntax.action_univs uu____13730
            FStar_Parser_Const.effect_Tot_lid uu____13734 [] pos
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
          FStar_Syntax_Syntax.sigattrs = [];
          FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
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
    let uu____13760 =
      let uu____13767 =
        let uu____13768 =
          let uu____13785 =
            let uu____13796 = FStar_Syntax_Syntax.as_arg t  in [uu____13796]
             in
          (reify_1, uu____13785)  in
        FStar_Syntax_Syntax.Tm_app uu____13768  in
      FStar_Syntax_Syntax.mk uu____13767  in
    uu____13760 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____13848 =
        let uu____13855 =
          let uu____13856 =
            let uu____13857 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____13857  in
          FStar_Syntax_Syntax.Tm_constant uu____13856  in
        FStar_Syntax_Syntax.mk uu____13855  in
      uu____13848 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____13859 =
      let uu____13866 =
        let uu____13867 =
          let uu____13884 =
            let uu____13895 = FStar_Syntax_Syntax.as_arg t  in [uu____13895]
             in
          (reflect_, uu____13884)  in
        FStar_Syntax_Syntax.Tm_app uu____13867  in
      FStar_Syntax_Syntax.mk uu____13866  in
    uu____13859 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13939 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____13964 = unfold_lazy i  in delta_qualifier uu____13964
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____13966 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____13967 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____13968 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____13991 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14004 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14005 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14012 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14013 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14029) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14034;
           FStar_Syntax_Syntax.index = uu____14035;
           FStar_Syntax_Syntax.sort = t2;_},uu____14037)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14046) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14052,uu____14053) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14095) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14120,t2,uu____14122) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14147,t2) -> delta_qualifier t2
  
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
    let uu____14186 = delta_qualifier t  in incr_delta_depth uu____14186
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14194 =
      let uu____14195 = FStar_Syntax_Subst.compress t  in
      uu____14195.FStar_Syntax_Syntax.n  in
    match uu____14194 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14200 -> false
  
let rec apply_last :
  'Auu____14209 .
    ('Auu____14209 -> 'Auu____14209) ->
      'Auu____14209 Prims.list -> 'Auu____14209 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14235 = f a  in [uu____14235]
      | x::xs -> let uu____14240 = apply_last f xs  in x :: uu____14240
  
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
  
let (mk_list :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term)
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____14295 =
            let uu____14302 =
              let uu____14303 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14303  in
            FStar_Syntax_Syntax.mk uu____14302  in
          uu____14295 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____14317 =
            let uu____14322 =
              let uu____14323 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14323
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14322 args  in
          uu____14317 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14337 =
            let uu____14342 =
              let uu____14343 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14343
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14342 args  in
          uu____14337 FStar_Pervasives_Native.None pos  in
        let uu____14344 =
          let uu____14345 =
            let uu____14346 = FStar_Syntax_Syntax.iarg typ  in [uu____14346]
             in
          nil uu____14345 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14380 =
                 let uu____14381 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14390 =
                   let uu____14401 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14410 =
                     let uu____14421 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14421]  in
                   uu____14401 :: uu____14410  in
                 uu____14381 :: uu____14390  in
               cons1 uu____14380 t.FStar_Syntax_Syntax.pos) l uu____14344
  
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
        | uu____14530 -> false
  
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
          | uu____14644 -> false
  
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
        | uu____14810 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____14848 = FStar_ST.op_Bang debug_term_eq  in
          if uu____14848
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
        let t11 = let uu____15052 = unmeta_safe t1  in canon_app uu____15052
           in
        let t21 = let uu____15058 = unmeta_safe t2  in canon_app uu____15058
           in
        let uu____15061 =
          let uu____15066 =
            let uu____15067 =
              let uu____15070 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15070  in
            uu____15067.FStar_Syntax_Syntax.n  in
          let uu____15071 =
            let uu____15072 =
              let uu____15075 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15075  in
            uu____15072.FStar_Syntax_Syntax.n  in
          (uu____15066, uu____15071)  in
        match uu____15061 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15077,uu____15078) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15087,FStar_Syntax_Syntax.Tm_uinst uu____15088) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15097,uu____15098) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15123,FStar_Syntax_Syntax.Tm_delayed uu____15124) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15149,uu____15150) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15179,FStar_Syntax_Syntax.Tm_ascribed uu____15180) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15219 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15219
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15224 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15224
        | (FStar_Syntax_Syntax.Tm_type
           uu____15227,FStar_Syntax_Syntax.Tm_type uu____15228) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15286 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15286) &&
              (let uu____15296 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15296)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15345 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15345) &&
              (let uu____15355 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15355)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15372 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15372) &&
              (let uu____15376 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15376)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15433 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15433) &&
              (let uu____15437 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15437)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15526 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15526) &&
              (let uu____15530 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15530)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15547,uu____15548) ->
            let uu____15549 =
              let uu____15551 = unlazy t11  in
              term_eq_dbg dbg uu____15551 t21  in
            check "lazy_l" uu____15549
        | (uu____15553,FStar_Syntax_Syntax.Tm_lazy uu____15554) ->
            let uu____15555 =
              let uu____15557 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15557  in
            check "lazy_r" uu____15555
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15602 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15602))
              &&
              (let uu____15606 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15606)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15610),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15612)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15670 =
               let uu____15672 = eq_quoteinfo qi1 qi2  in uu____15672 = Equal
                in
             check "tm_quoted qi" uu____15670) &&
              (let uu____15675 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15675)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15705 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15705) &&
                   (let uu____15709 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15709)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15728 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15728) &&
                    (let uu____15732 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15732))
                   &&
                   (let uu____15736 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15736)
             | uu____15739 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15745) -> fail "unk"
        | (uu____15747,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15749,uu____15750) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15752,uu____15753) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15755,uu____15756) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15758,uu____15759) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15761,uu____15762) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15764,uu____15765) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15785,uu____15786) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15802,uu____15803) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15811,uu____15812) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15830,uu____15831) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____15855,uu____15856) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____15871,uu____15872) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____15886,uu____15887) ->
            fail "bottom"
        | (uu____15895,FStar_Syntax_Syntax.Tm_bvar uu____15896) ->
            fail "bottom"
        | (uu____15898,FStar_Syntax_Syntax.Tm_name uu____15899) ->
            fail "bottom"
        | (uu____15901,FStar_Syntax_Syntax.Tm_fvar uu____15902) ->
            fail "bottom"
        | (uu____15904,FStar_Syntax_Syntax.Tm_constant uu____15905) ->
            fail "bottom"
        | (uu____15907,FStar_Syntax_Syntax.Tm_type uu____15908) ->
            fail "bottom"
        | (uu____15910,FStar_Syntax_Syntax.Tm_abs uu____15911) ->
            fail "bottom"
        | (uu____15931,FStar_Syntax_Syntax.Tm_arrow uu____15932) ->
            fail "bottom"
        | (uu____15948,FStar_Syntax_Syntax.Tm_refine uu____15949) ->
            fail "bottom"
        | (uu____15957,FStar_Syntax_Syntax.Tm_app uu____15958) ->
            fail "bottom"
        | (uu____15976,FStar_Syntax_Syntax.Tm_match uu____15977) ->
            fail "bottom"
        | (uu____16001,FStar_Syntax_Syntax.Tm_let uu____16002) ->
            fail "bottom"
        | (uu____16017,FStar_Syntax_Syntax.Tm_uvar uu____16018) ->
            fail "bottom"
        | (uu____16032,FStar_Syntax_Syntax.Tm_meta uu____16033) ->
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
               let uu____16068 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16068)
          (fun q1  ->
             fun q2  ->
               let uu____16080 =
                 let uu____16082 = eq_aqual q1 q2  in uu____16082 = Equal  in
               check "arg qual" uu____16080) a1 a2

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
               let uu____16107 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16107)
          (fun q1  ->
             fun q2  ->
               let uu____16119 =
                 let uu____16121 = eq_aqual q1 q2  in uu____16121 = Equal  in
               check "binder qual" uu____16119) b1 b2

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
        ((let uu____16135 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16135) &&
           (let uu____16139 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16139))
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
    fun uu____16149  ->
      fun uu____16150  ->
        match (uu____16149, uu____16150) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16277 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16277) &&
               (let uu____16281 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16281))
              &&
              (let uu____16285 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16327 -> false  in
               check "branch when" uu____16285)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16348 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16348) &&
           (let uu____16357 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16357))
          &&
          (let uu____16361 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16361)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16378 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16378 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16432 ->
        let uu____16455 =
          let uu____16457 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16457  in
        Prims.int_one + uu____16455
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16460 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16460
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16464 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16464
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16473 = sizeof t1  in (FStar_List.length us) + uu____16473
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16477) ->
        let uu____16502 = sizeof t1  in
        let uu____16504 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16519  ->
                 match uu____16519 with
                 | (bv,uu____16529) ->
                     let uu____16534 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16534) Prims.int_zero bs
           in
        uu____16502 + uu____16504
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____16563 = sizeof hd1  in
        let uu____16565 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16580  ->
                 match uu____16580 with
                 | (arg,uu____16590) ->
                     let uu____16595 = sizeof arg  in acc + uu____16595)
            Prims.int_zero args
           in
        uu____16563 + uu____16565
    | uu____16598 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16612 =
        let uu____16613 = un_uinst t  in uu____16613.FStar_Syntax_Syntax.n
         in
      match uu____16612 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16618 -> false
  
let (is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  -> is_fvar FStar_Parser_Const.synth_lid t 
let (has_attribute :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Ident.lident -> Prims.bool)
  = fun attrs  -> fun attr  -> FStar_Util.for_some (is_fvar attr) attrs 
let (get_attribute :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.args FStar_Pervasives_Native.option)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.tryPick
        (fun t  ->
           let uu____16679 = head_and_args t  in
           match uu____16679 with
           | (head1,args) ->
               let uu____16734 =
                 let uu____16735 = FStar_Syntax_Subst.compress head1  in
                 uu____16735.FStar_Syntax_Syntax.n  in
               (match uu____16734 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16761 -> FStar_Pervasives_Native.None)) attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options1 s =
        let uu____16791 = FStar_Options.set_options s  in
        match uu____16791 with
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
          ((let uu____16805 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16805 (fun a1  -> ()));
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
          let uu____16820 = FStar_Options.internal_pop ()  in
          if uu____16820
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
    | FStar_Syntax_Syntax.Tm_delayed uu____16852 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____16879 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____16894 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____16895 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____16896 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16905) ->
        let uu____16930 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____16930 with
         | (bs1,t2) ->
             let uu____16939 =
               FStar_List.collect
                 (fun uu____16951  ->
                    match uu____16951 with
                    | (b,uu____16961) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____16966 = unbound_variables t2  in
             FStar_List.append uu____16939 uu____16966)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____16991 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____16991 with
         | (bs1,c1) ->
             let uu____17000 =
               FStar_List.collect
                 (fun uu____17012  ->
                    match uu____17012 with
                    | (b,uu____17022) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17027 = unbound_variables_comp c1  in
             FStar_List.append uu____17000 uu____17027)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17036 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17036 with
         | (bs,t2) ->
             let uu____17059 =
               FStar_List.collect
                 (fun uu____17071  ->
                    match uu____17071 with
                    | (b1,uu____17081) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17086 = unbound_variables t2  in
             FStar_List.append uu____17059 uu____17086)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17115 =
          FStar_List.collect
            (fun uu____17129  ->
               match uu____17129 with
               | (x,uu____17141) -> unbound_variables x) args
           in
        let uu____17150 = unbound_variables t1  in
        FStar_List.append uu____17115 uu____17150
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17191 = unbound_variables t1  in
        let uu____17194 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17209 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17209 with
                  | (p,wopt,t2) ->
                      let uu____17231 = unbound_variables t2  in
                      let uu____17234 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17231 uu____17234))
           in
        FStar_List.append uu____17191 uu____17194
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17248) ->
        let uu____17289 = unbound_variables t1  in
        let uu____17292 =
          let uu____17295 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17326 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17295 uu____17326  in
        FStar_List.append uu____17289 uu____17292
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17367 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17370 =
          let uu____17373 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17376 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17381 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17383 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17383 with
                 | (uu____17404,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17373 uu____17376  in
        FStar_List.append uu____17367 uu____17370
    | FStar_Syntax_Syntax.Tm_let ((uu____17406,lbs),t1) ->
        let uu____17426 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17426 with
         | (lbs1,t2) ->
             let uu____17441 = unbound_variables t2  in
             let uu____17444 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17451 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17454 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17451 uu____17454) lbs1
                in
             FStar_List.append uu____17441 uu____17444)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17471 = unbound_variables t1  in
        let uu____17474 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17479,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17534  ->
                      match uu____17534 with
                      | (a,uu____17546) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17555,uu____17556,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17562,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17568 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17577 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17578 -> []  in
        FStar_List.append uu____17471 uu____17474

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17585) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17595) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17605 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17608 =
          FStar_List.collect
            (fun uu____17622  ->
               match uu____17622 with
               | (a,uu____17634) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17605 uu____17608

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
            let uu____17749 = head_and_args h  in
            (match uu____17749 with
             | (head1,args) ->
                 let uu____17810 =
                   let uu____17811 = FStar_Syntax_Subst.compress head1  in
                   uu____17811.FStar_Syntax_Syntax.n  in
                 (match uu____17810 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____17864 -> aux (h :: acc) t))
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
      let uu____17888 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____17888 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2459_17930 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2459_17930.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2459_17930.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2459_17930.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2459_17930.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2459_17930.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____17938 =
      let uu____17939 = FStar_Syntax_Subst.compress t  in
      uu____17939.FStar_Syntax_Syntax.n  in
    match uu____17938 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____17943,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____17971)::uu____17972 ->
                  let pats' = unmeta pats  in
                  let uu____18032 = head_and_args pats'  in
                  (match uu____18032 with
                   | (head1,uu____18051) ->
                       let uu____18076 =
                         let uu____18077 = un_uinst head1  in
                         uu____18077.FStar_Syntax_Syntax.n  in
                       (match uu____18076 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18082 -> false))
              | uu____18084 -> false)
         | uu____18096 -> false)
    | uu____18098 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18114 =
      let uu____18131 = unmeta e  in head_and_args uu____18131  in
    match uu____18114 with
    | (head1,args) ->
        let uu____18162 =
          let uu____18177 =
            let uu____18178 = un_uinst head1  in
            uu____18178.FStar_Syntax_Syntax.n  in
          (uu____18177, args)  in
        (match uu____18162 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18196) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18220::(hd1,uu____18222)::(tl1,uu____18224)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18291 =
               let uu____18294 =
                 let uu____18297 = list_elements tl1  in
                 FStar_Util.must uu____18297  in
               hd1 :: uu____18294  in
             FStar_Pervasives_Native.Some uu____18291
         | uu____18306 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18335 =
      let uu____18336 = FStar_Syntax_Subst.compress t  in
      uu____18336.FStar_Syntax_Syntax.n  in
    match uu____18335 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18343) ->
        let uu____18378 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18378 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18412 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18412
             then
               let uu____18419 =
                 let uu____18430 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18430]  in
               mk_app t uu____18419
             else e1)
    | uu____18457 ->
        let uu____18458 =
          let uu____18469 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18469]  in
        mk_app t uu____18458
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18524 = list_elements e  in
        match uu____18524 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18559 =
          let uu____18576 = unmeta p  in
          FStar_All.pipe_right uu____18576 head_and_args  in
        match uu____18559 with
        | (head1,args) ->
            let uu____18627 =
              let uu____18642 =
                let uu____18643 = un_uinst head1  in
                uu____18643.FStar_Syntax_Syntax.n  in
              (uu____18642, args)  in
            (match uu____18627 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18665,uu____18666)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18718 ->
                 let uu____18733 =
                   let uu____18739 =
                     let uu____18741 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18741
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____18739)  in
                 FStar_Errors.raise_error uu____18733
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____18784 =
            let uu____18801 = unmeta t1  in
            FStar_All.pipe_right uu____18801 head_and_args  in
          match uu____18784 with
          | (head1,args) ->
              let uu____18848 =
                let uu____18863 =
                  let uu____18864 = un_uinst head1  in
                  uu____18864.FStar_Syntax_Syntax.n  in
                (uu____18863, args)  in
              (match uu____18848 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____18883)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____18920 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____18950 = smt_pat_or1 t1  in
            (match uu____18950 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____18972 = list_elements1 e  in
                 FStar_All.pipe_right uu____18972
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19002 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19002
                           (FStar_List.map one_pat)))
             | uu____19031 ->
                 let uu____19036 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19036])
        | uu____19091 ->
            let uu____19094 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19094]
         in
      let uu____19149 =
        let uu____19182 =
          let uu____19183 = FStar_Syntax_Subst.compress t  in
          uu____19183.FStar_Syntax_Syntax.n  in
        match uu____19182 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19240 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19240 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19311;
                        FStar_Syntax_Syntax.effect_name = uu____19312;
                        FStar_Syntax_Syntax.result_typ = uu____19313;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19315)::(post,uu____19317)::(pats,uu____19319)::[];
                        FStar_Syntax_Syntax.flags = uu____19320;_}
                      ->
                      let uu____19381 = lemma_pats pats  in
                      (binders1, pre, post, uu____19381)
                  | uu____19418 -> failwith "impos"))
        | uu____19452 -> failwith "Impos"  in
      match uu____19149 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19544 =
              let uu____19551 =
                let uu____19552 =
                  let uu____19559 = mk_imp pre post1  in
                  let uu____19562 =
                    let uu____19563 =
                      let uu____19584 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19584, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19563  in
                  (uu____19559, uu____19562)  in
                FStar_Syntax_Syntax.Tm_meta uu____19552  in
              FStar_Syntax_Syntax.mk uu____19551  in
            uu____19544 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19608 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19608 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19638 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19649 -> true
    | uu____19651 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19662 -> true
    | uu____19664 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19682 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19683 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19684 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19685 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19686 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19687 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19688 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19689 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19692 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19695 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19682;
        FStar_Syntax_Syntax.bind_wp = uu____19683;
        FStar_Syntax_Syntax.stronger = uu____19684;
        FStar_Syntax_Syntax.if_then_else = uu____19685;
        FStar_Syntax_Syntax.ite_wp = uu____19686;
        FStar_Syntax_Syntax.close_wp = uu____19687;
        FStar_Syntax_Syntax.trivial = uu____19688;
        FStar_Syntax_Syntax.repr = uu____19689;
        FStar_Syntax_Syntax.return_repr = uu____19692;
        FStar_Syntax_Syntax.bind_repr = uu____19695
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____19727 =
        match uu____19727 with
        | (ts1,ts2) ->
            let uu____19738 = f ts1  in
            let uu____19739 = f ts2  in (uu____19738, uu____19739)
         in
      let uu____19740 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____19745 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____19750 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____19755 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____19760 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____19740;
        FStar_Syntax_Syntax.l_return = uu____19745;
        FStar_Syntax_Syntax.l_bind = uu____19750;
        FStar_Syntax_Syntax.l_subcomp = uu____19755;
        FStar_Syntax_Syntax.l_if_then_else = uu____19760
      }
  
let (apply_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.eff_combinators ->
      FStar_Syntax_Syntax.eff_combinators)
  =
  fun f  ->
    fun combs  ->
      match combs with
      | FStar_Syntax_Syntax.Primitive_eff combs1 ->
          let uu____19782 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____19782
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19784 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____19784
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19786 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____19786
  
let (get_wp_close_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStar_Syntax_Syntax.close_wp)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStar_Syntax_Syntax.close_wp)
    | uu____19801 -> FStar_Pervasives_Native.None
  
let (get_eff_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.repr
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19815 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19815
          (fun _19822  -> FStar_Pervasives_Native.Some _19822)
  
let (get_bind_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.bind_wp
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.bind_wp
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
          FStar_Pervasives_Native.snd
  
let (get_return_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.ret_wp
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.ret_wp
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
          FStar_Pervasives_Native.snd
  
let (get_bind_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.bind_repr
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.bind_repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19862 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19862
          (fun _19869  -> FStar_Pervasives_Native.Some _19869)
  
let (get_return_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.return_repr
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.return_repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19883 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19883
          (fun _19890  -> FStar_Pervasives_Native.Some _19890)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun _19904  -> FStar_Pervasives_Native.Some _19904)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun _19908  -> FStar_Pervasives_Native.Some _19908)
    | uu____19909 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19921 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19921
          (fun _19928  -> FStar_Pervasives_Native.Some _19928)
    | uu____19929 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun _19943  -> FStar_Pervasives_Native.Some _19943)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun _19947  -> FStar_Pervasives_Native.Some _19947)
    | uu____19948 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun _19962  -> FStar_Pervasives_Native.Some _19962)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun _19966  -> FStar_Pervasives_Native.Some _19966)
    | uu____19967 -> FStar_Pervasives_Native.None
  
let (get_stronger_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.stronger
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.stronger
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
          FStar_Pervasives_Native.snd
  
let (get_stronger_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff uu____19991 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____19992 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19994 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19994
          (fun _20001  -> FStar_Pervasives_Native.Some _20001)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun _20015  -> FStar_Pervasives_Native.Some _20015)
    | uu____20016 -> FStar_Pervasives_Native.None
  