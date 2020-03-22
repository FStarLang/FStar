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
  
let rec (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5284,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5291) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5296,lids) -> lids
    | FStar_Syntax_Syntax.Sig_group ses ->
        FStar_List.concatMap lids_of_sigelt ses
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5310,uu____5311,uu____5312,uu____5313,uu____5314) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5324,uu____5325,uu____5326,uu____5327) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5333,uu____5334,uu____5335,uu____5336,uu____5337) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5345,uu____5346) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5348,uu____5349) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5351 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5352 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5353 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5354 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    let uu____5375 = lids_of_sigelt se  in
    match uu____5375 with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5381 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5407  ->
    match uu___7_5407 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5421 'Auu____5422 .
    ('Auu____5421 FStar_Syntax_Syntax.syntax * 'Auu____5422) ->
      FStar_Range.range
  =
  fun uu____5433  ->
    match uu____5433 with | (hd1,uu____5441) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5455 'Auu____5456 .
    ('Auu____5455 FStar_Syntax_Syntax.syntax * 'Auu____5456) Prims.list ->
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
      | uu____5554 ->
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
      let uu____5613 =
        FStar_List.map
          (fun uu____5640  ->
             match uu____5640 with
             | (bv,aq) ->
                 let uu____5659 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5659, aq)) bs
         in
      mk_app f uu____5613
  
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
          let uu____5709 = FStar_Ident.range_of_lid l  in
          let uu____5710 =
            let uu____5719 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5719  in
          uu____5710 FStar_Pervasives_Native.None uu____5709
      | uu____5724 ->
          let e =
            let uu____5738 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5738 args  in
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
          let uu____5815 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5815
          then
            let uu____5818 =
              let uu____5824 =
                let uu____5826 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5826  in
              let uu____5829 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5824, uu____5829)  in
            FStar_Ident.mk_ident uu____5818
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___945_5834 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___945_5834.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___945_5834.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5835 = mk_field_projector_name_from_ident lid nm  in
        (uu____5835, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5847) -> ses
    | uu____5856 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5871 = FStar_Syntax_Unionfind.find uv  in
      match uu____5871 with
      | FStar_Pervasives_Native.Some uu____5874 ->
          let uu____5875 =
            let uu____5877 =
              let uu____5879 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5879  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5877  in
          failwith uu____5875
      | uu____5884 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____5967 -> q1 = q2
  
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
              let uu____6013 =
                let uu___1002_6014 = rc  in
                let uu____6015 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1002_6014.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6015;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1002_6014.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6013
           in
        match bs with
        | [] -> t
        | uu____6032 ->
            let body =
              let uu____6034 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6034  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6064 =
                   let uu____6071 =
                     let uu____6072 =
                       let uu____6091 =
                         let uu____6100 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6100 bs'  in
                       let uu____6115 = close_lopt lopt'  in
                       (uu____6091, t1, uu____6115)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6072  in
                   FStar_Syntax_Syntax.mk uu____6071  in
                 uu____6064 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6130 ->
                 let uu____6131 =
                   let uu____6138 =
                     let uu____6139 =
                       let uu____6158 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6167 = close_lopt lopt  in
                       (uu____6158, body, uu____6167)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6139  in
                   FStar_Syntax_Syntax.mk uu____6138  in
                 uu____6131 FStar_Pervasives_Native.None
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
      | uu____6223 ->
          let uu____6232 =
            let uu____6239 =
              let uu____6240 =
                let uu____6255 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6264 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6255, uu____6264)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6240  in
            FStar_Syntax_Syntax.mk uu____6239  in
          uu____6232 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6313 =
        let uu____6314 = FStar_Syntax_Subst.compress t  in
        uu____6314.FStar_Syntax_Syntax.n  in
      match uu____6313 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6344) ->
               let uu____6353 =
                 let uu____6354 = FStar_Syntax_Subst.compress tres  in
                 uu____6354.FStar_Syntax_Syntax.n  in
               (match uu____6353 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6397 -> t)
           | uu____6398 -> t)
      | uu____6399 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6417 =
        let uu____6418 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6418 t.FStar_Syntax_Syntax.pos  in
      let uu____6419 =
        let uu____6426 =
          let uu____6427 =
            let uu____6434 =
              let uu____6437 =
                let uu____6438 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6438]  in
              FStar_Syntax_Subst.close uu____6437 t  in
            (b, uu____6434)  in
          FStar_Syntax_Syntax.Tm_refine uu____6427  in
        FStar_Syntax_Syntax.mk uu____6426  in
      uu____6419 FStar_Pervasives_Native.None uu____6417
  
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
        let uu____6518 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6518 with
         | (bs1,c1) ->
             let uu____6537 = is_total_comp c1  in
             if uu____6537
             then
               let uu____6552 = arrow_formals_comp (comp_result c1)  in
               (match uu____6552 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6619;
           FStar_Syntax_Syntax.index = uu____6620;
           FStar_Syntax_Syntax.sort = s;_},uu____6622)
        ->
        let rec aux s1 k2 =
          let uu____6653 =
            let uu____6654 = FStar_Syntax_Subst.compress s1  in
            uu____6654.FStar_Syntax_Syntax.n  in
          match uu____6653 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6669 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6684;
                 FStar_Syntax_Syntax.index = uu____6685;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6687)
              -> aux s2 k2
          | uu____6695 ->
              let uu____6696 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6696)
           in
        aux s k1
    | uu____6711 ->
        let uu____6712 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6712)
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6747 = arrow_formals_comp k  in
    match uu____6747 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6889 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6889 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6913 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_6922  ->
                         match uu___8_6922 with
                         | FStar_Syntax_Syntax.DECREASES uu____6924 -> true
                         | uu____6928 -> false))
                  in
               (match uu____6913 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____6963 ->
                    let uu____6966 = is_total_comp c1  in
                    if uu____6966
                    then
                      let uu____6985 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____6985 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7078;
             FStar_Syntax_Syntax.index = uu____7079;
             FStar_Syntax_Syntax.sort = k2;_},uu____7081)
          -> arrow_until_decreases k2
      | uu____7089 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7110 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7110 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7164 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7185 =
                 FStar_Common.tabulate n_univs (fun uu____7191  -> false)  in
               let uu____7194 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7219  ->
                         match uu____7219 with
                         | (x,uu____7228) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7185 uu____7194)
           in
        ((n_univs + (FStar_List.length bs)), uu____7164)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7284 =
            let uu___1124_7285 = rc  in
            let uu____7286 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1124_7285.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7286;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1124_7285.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7284
      | uu____7295 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7329 =
        let uu____7330 =
          let uu____7333 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7333  in
        uu____7330.FStar_Syntax_Syntax.n  in
      match uu____7329 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7379 = aux t2 what  in
          (match uu____7379 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7451 -> ([], t1, abs_body_lcomp)  in
    let uu____7468 = aux t FStar_Pervasives_Native.None  in
    match uu____7468 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7516 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7516 with
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
                    | (FStar_Pervasives_Native.None ,uu____7679) -> def
                    | (uu____7690,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7702) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _7718  ->
                                  FStar_Syntax_Syntax.U_name _7718))
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
            let uu____7800 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7800 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7835 ->
            let t' = arrow binders c  in
            let uu____7847 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____7847 with
             | (uvs1,t'1) ->
                 let uu____7868 =
                   let uu____7869 = FStar_Syntax_Subst.compress t'1  in
                   uu____7869.FStar_Syntax_Syntax.n  in
                 (match uu____7868 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____7918 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____7943 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____7954 -> false
  
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
      let uu____8017 =
        let uu____8018 = pre_typ t  in uu____8018.FStar_Syntax_Syntax.n  in
      match uu____8017 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8023 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8037 =
        let uu____8038 = pre_typ t  in uu____8038.FStar_Syntax_Syntax.n  in
      match uu____8037 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8042 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8044) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8070) ->
          is_constructed_typ t1 lid
      | uu____8075 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8088 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8089 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8090 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8092) -> get_tycon t2
    | uu____8117 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8125 =
      let uu____8126 = un_uinst t  in uu____8126.FStar_Syntax_Syntax.n  in
    match uu____8125 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8131 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8145 =
        let uu____8149 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8149  in
      match uu____8145 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8181 -> false
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
  fun uu____8200  ->
    let u =
      let uu____8206 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _8223  -> FStar_Syntax_Syntax.U_unif _8223)
        uu____8206
       in
    let uu____8224 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8224, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8237 = eq_tm a a'  in
      match uu____8237 with | Equal  -> true | uu____8240 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8245 =
    let uu____8252 =
      let uu____8253 =
        let uu____8254 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8254
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8253  in
    FStar_Syntax_Syntax.mk uu____8252  in
  uu____8245 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
let (rename_let_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.rename_let_attr 
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
          let uu____8367 =
            let uu____8370 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8371 =
              let uu____8378 =
                let uu____8379 =
                  let uu____8396 =
                    let uu____8407 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8416 =
                      let uu____8427 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8427]  in
                    uu____8407 :: uu____8416  in
                  (tand, uu____8396)  in
                FStar_Syntax_Syntax.Tm_app uu____8379  in
              FStar_Syntax_Syntax.mk uu____8378  in
            uu____8371 FStar_Pervasives_Native.None uu____8370  in
          FStar_Pervasives_Native.Some uu____8367
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8504 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8505 =
          let uu____8512 =
            let uu____8513 =
              let uu____8530 =
                let uu____8541 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8550 =
                  let uu____8561 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8561]  in
                uu____8541 :: uu____8550  in
              (op_t, uu____8530)  in
            FStar_Syntax_Syntax.Tm_app uu____8513  in
          FStar_Syntax_Syntax.mk uu____8512  in
        uu____8505 FStar_Pervasives_Native.None uu____8504
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8618 =
      let uu____8625 =
        let uu____8626 =
          let uu____8643 =
            let uu____8654 = FStar_Syntax_Syntax.as_arg phi  in [uu____8654]
             in
          (t_not, uu____8643)  in
        FStar_Syntax_Syntax.Tm_app uu____8626  in
      FStar_Syntax_Syntax.mk uu____8625  in
    uu____8618 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____8851 =
      let uu____8858 =
        let uu____8859 =
          let uu____8876 =
            let uu____8887 = FStar_Syntax_Syntax.as_arg e  in [uu____8887]
             in
          (b2t_v, uu____8876)  in
        FStar_Syntax_Syntax.Tm_app uu____8859  in
      FStar_Syntax_Syntax.mk uu____8858  in
    uu____8851 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____8934 = head_and_args e  in
    match uu____8934 with
    | (hd1,args) ->
        let uu____8979 =
          let uu____8994 =
            let uu____8995 = FStar_Syntax_Subst.compress hd1  in
            uu____8995.FStar_Syntax_Syntax.n  in
          (uu____8994, args)  in
        (match uu____8979 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9012)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9047 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9069 =
      let uu____9070 = unmeta t  in uu____9070.FStar_Syntax_Syntax.n  in
    match uu____9069 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9075 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9098 = is_t_true t1  in
      if uu____9098
      then t2
      else
        (let uu____9105 = is_t_true t2  in
         if uu____9105 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9133 = is_t_true t1  in
      if uu____9133
      then t_true
      else
        (let uu____9140 = is_t_true t2  in
         if uu____9140 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9169 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9170 =
        let uu____9177 =
          let uu____9178 =
            let uu____9195 =
              let uu____9206 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9215 =
                let uu____9226 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9226]  in
              uu____9206 :: uu____9215  in
            (teq, uu____9195)  in
          FStar_Syntax_Syntax.Tm_app uu____9178  in
        FStar_Syntax_Syntax.mk uu____9177  in
      uu____9170 FStar_Pervasives_Native.None uu____9169
  
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
          let uu____9293 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9294 =
            let uu____9301 =
              let uu____9302 =
                let uu____9319 =
                  let uu____9330 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9339 =
                    let uu____9350 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9359 =
                      let uu____9370 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9370]  in
                    uu____9350 :: uu____9359  in
                  uu____9330 :: uu____9339  in
                (eq_inst, uu____9319)  in
              FStar_Syntax_Syntax.Tm_app uu____9302  in
            FStar_Syntax_Syntax.mk uu____9301  in
          uu____9294 FStar_Pervasives_Native.None uu____9293
  
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
        let uu____9447 =
          let uu____9454 =
            let uu____9455 =
              let uu____9472 =
                let uu____9483 = FStar_Syntax_Syntax.iarg t  in
                let uu____9492 =
                  let uu____9503 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9512 =
                    let uu____9523 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9523]  in
                  uu____9503 :: uu____9512  in
                uu____9483 :: uu____9492  in
              (t_has_type1, uu____9472)  in
            FStar_Syntax_Syntax.Tm_app uu____9455  in
          FStar_Syntax_Syntax.mk uu____9454  in
        uu____9447 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9600 =
          let uu____9607 =
            let uu____9608 =
              let uu____9625 =
                let uu____9636 = FStar_Syntax_Syntax.iarg t  in
                let uu____9645 =
                  let uu____9656 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9656]  in
                uu____9636 :: uu____9645  in
              (t_with_type1, uu____9625)  in
            FStar_Syntax_Syntax.Tm_app uu____9608  in
          FStar_Syntax_Syntax.mk uu____9607  in
        uu____9600 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9703 =
    let uu____9710 =
      let uu____9711 =
        let uu____9718 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9718, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9711  in
    FStar_Syntax_Syntax.mk uu____9710  in
  uu____9703 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
        let uu____9801 =
          let uu____9808 =
            let uu____9809 =
              let uu____9826 =
                let uu____9837 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____9846 =
                  let uu____9857 =
                    let uu____9866 =
                      let uu____9867 =
                        let uu____9868 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____9868]  in
                      abs uu____9867 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____9866  in
                  [uu____9857]  in
                uu____9837 :: uu____9846  in
              (fa, uu____9826)  in
            FStar_Syntax_Syntax.Tm_app uu____9809  in
          FStar_Syntax_Syntax.mk uu____9808  in
        uu____9801 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____9995 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____9995
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10014 -> true
    | uu____10016 -> false
  
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
          let uu____10063 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10063, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10092 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10092, FStar_Pervasives_Native.None, t2)  in
        let uu____10106 =
          let uu____10107 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10107  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10106
  
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
      let uu____10183 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10186 =
        let uu____10197 = FStar_Syntax_Syntax.as_arg p  in [uu____10197]  in
      mk_app uu____10183 uu____10186
  
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
      let uu____10237 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10240 =
        let uu____10251 = FStar_Syntax_Syntax.as_arg p  in [uu____10251]  in
      mk_app uu____10237 uu____10240
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10286 = head_and_args t  in
    match uu____10286 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____10335 =
          let uu____10350 =
            let uu____10351 = FStar_Syntax_Subst.compress head3  in
            uu____10351.FStar_Syntax_Syntax.n  in
          (uu____10350, args)  in
        (match uu____10335 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10370)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10436 =
                    let uu____10441 =
                      let uu____10442 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10442]  in
                    FStar_Syntax_Subst.open_term uu____10441 p  in
                  (match uu____10436 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10499 -> failwith "impossible"  in
                       let uu____10507 =
                         let uu____10509 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10509
                          in
                       if uu____10507
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10525 -> FStar_Pervasives_Native.None)
         | uu____10528 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10559 = head_and_args t  in
    match uu____10559 with
    | (head1,args) ->
        let uu____10610 =
          let uu____10625 =
            let uu____10626 = FStar_Syntax_Subst.compress head1  in
            uu____10626.FStar_Syntax_Syntax.n  in
          (uu____10625, args)  in
        (match uu____10610 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10648;
               FStar_Syntax_Syntax.vars = uu____10649;_},u::[]),(t1,uu____10652)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10699 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10734 = head_and_args t  in
    match uu____10734 with
    | (head1,args) ->
        let uu____10785 =
          let uu____10800 =
            let uu____10801 = FStar_Syntax_Subst.compress head1  in
            uu____10801.FStar_Syntax_Syntax.n  in
          (uu____10800, args)  in
        (match uu____10785 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10823;
               FStar_Syntax_Syntax.vars = uu____10824;_},u::[]),(t1,uu____10827)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10874 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____10902 =
      let uu____10919 = unmeta t  in head_and_args uu____10919  in
    match uu____10902 with
    | (head1,uu____10922) ->
        let uu____10947 =
          let uu____10948 = un_uinst head1  in
          uu____10948.FStar_Syntax_Syntax.n  in
        (match uu____10947 with
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
         | uu____10953 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10973 =
      let uu____10974 = FStar_Syntax_Subst.compress t  in
      uu____10974.FStar_Syntax_Syntax.n  in
    match uu____10973 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11080 =
          let uu____11085 =
            let uu____11086 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11086  in
          (b, uu____11085)  in
        FStar_Pervasives_Native.Some uu____11080
    | uu____11091 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11114 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11114
      (fun uu____11142  ->
         match uu____11142 with
         | (b,c) ->
             let uu____11161 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11161 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11224 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11261 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11261
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11313 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11356 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11397 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11783) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11795) ->
          unmeta_monadic t
      | uu____11808 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____11877 =
        match uu____11877 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____11915  ->
                   match uu____11915 with
                   | (lid,out_lid) ->
                       let uu____11924 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____11924
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____11951 = head_and_args t  in
      match uu____11951 with
      | (hd1,args) ->
          let uu____11996 =
            let uu____11997 = un_uinst hd1  in
            uu____11997.FStar_Syntax_Syntax.n  in
          (match uu____11996 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12003 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12012 = un_squash t  in
      FStar_Util.bind_opt uu____12012
        (fun t1  ->
           let uu____12028 = head_and_args' t1  in
           match uu____12028 with
           | (hd1,args) ->
               let uu____12067 =
                 let uu____12068 = un_uinst hd1  in
                 uu____12068.FStar_Syntax_Syntax.n  in
               (match uu____12067 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12074 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12115,pats)) ->
          let uu____12153 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12153)
      | uu____12166 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12233 = head_and_args t1  in
        match uu____12233 with
        | (t2,args) ->
            let uu____12288 = un_uinst t2  in
            let uu____12289 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12330  ->
                      match uu____12330 with
                      | (t3,imp) ->
                          let uu____12349 = unascribe t3  in
                          (uu____12349, imp)))
               in
            (uu____12288, uu____12289)
         in
      let rec aux qopt out t1 =
        let uu____12400 = let uu____12424 = flat t1  in (qopt, uu____12424)
           in
        match uu____12400 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12464;
                 FStar_Syntax_Syntax.vars = uu____12465;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12468);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12469;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12470;_},uu____12471)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12573;
                 FStar_Syntax_Syntax.vars = uu____12574;_},uu____12575::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12578);
                  FStar_Syntax_Syntax.pos = uu____12579;
                  FStar_Syntax_Syntax.vars = uu____12580;_},uu____12581)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12698;
               FStar_Syntax_Syntax.vars = uu____12699;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12702);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12703;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12704;_},uu____12705)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12798 =
              let uu____12802 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12802  in
            aux uu____12798 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12812;
               FStar_Syntax_Syntax.vars = uu____12813;_},uu____12814::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12817);
                FStar_Syntax_Syntax.pos = uu____12818;
                FStar_Syntax_Syntax.vars = uu____12819;_},uu____12820)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12929 =
              let uu____12933 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12933  in
            aux uu____12929 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____12943) ->
            let bs = FStar_List.rev out  in
            let uu____12996 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____12996 with
             | (bs1,t2) ->
                 let uu____13005 = patterns t2  in
                 (match uu____13005 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13055 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13110 = un_squash t  in
      FStar_Util.bind_opt uu____13110
        (fun t1  ->
           let uu____13125 = arrow_one t1  in
           match uu____13125 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13140 =
                 let uu____13142 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13142  in
               if uu____13140
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13152 = comp_to_comp_typ_nouniv c  in
                    uu____13152.FStar_Syntax_Syntax.result_typ  in
                  let uu____13153 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13153
                  then
                    let uu____13160 = patterns q  in
                    match uu____13160 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13223 =
                       let uu____13224 =
                         let uu____13229 =
                           let uu____13230 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13241 =
                             let uu____13252 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13252]  in
                           uu____13230 :: uu____13241  in
                         (FStar_Parser_Const.imp_lid, uu____13229)  in
                       BaseConn uu____13224  in
                     FStar_Pervasives_Native.Some uu____13223))
           | uu____13285 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13293 = un_squash t  in
      FStar_Util.bind_opt uu____13293
        (fun t1  ->
           let uu____13324 = head_and_args' t1  in
           match uu____13324 with
           | (hd1,args) ->
               let uu____13363 =
                 let uu____13378 =
                   let uu____13379 = un_uinst hd1  in
                   uu____13379.FStar_Syntax_Syntax.n  in
                 (uu____13378, args)  in
               (match uu____13363 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13396)::(a2,uu____13398)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13449 =
                      let uu____13450 = FStar_Syntax_Subst.compress a2  in
                      uu____13450.FStar_Syntax_Syntax.n  in
                    (match uu____13449 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13457) ->
                         let uu____13492 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13492 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13545 -> failwith "impossible"  in
                              let uu____13553 = patterns q1  in
                              (match uu____13553 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13614 -> FStar_Pervasives_Native.None)
                | uu____13615 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13638 = destruct_sq_forall phi  in
          (match uu____13638 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13648  -> FStar_Pervasives_Native.Some _13648)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13655 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13661 = destruct_sq_exists phi  in
          (match uu____13661 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13671  -> FStar_Pervasives_Native.Some _13671)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13678 -> f1)
      | uu____13681 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13685 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13685
      (fun uu____13690  ->
         let uu____13691 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13691
           (fun uu____13696  ->
              let uu____13697 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13697
                (fun uu____13702  ->
                   let uu____13703 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13703
                     (fun uu____13708  ->
                        let uu____13709 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13709
                          (fun uu____13713  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13731 =
            let uu____13736 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13736  in
          let uu____13737 =
            let uu____13738 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13738  in
          let uu____13741 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13731 a.FStar_Syntax_Syntax.action_univs uu____13737
            FStar_Parser_Const.effect_Tot_lid uu____13741 [] pos
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
    let uu____13767 =
      let uu____13774 =
        let uu____13775 =
          let uu____13792 =
            let uu____13803 = FStar_Syntax_Syntax.as_arg t  in [uu____13803]
             in
          (reify_1, uu____13792)  in
        FStar_Syntax_Syntax.Tm_app uu____13775  in
      FStar_Syntax_Syntax.mk uu____13774  in
    uu____13767 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____13855 =
        let uu____13862 =
          let uu____13863 =
            let uu____13864 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____13864  in
          FStar_Syntax_Syntax.Tm_constant uu____13863  in
        FStar_Syntax_Syntax.mk uu____13862  in
      uu____13855 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____13866 =
      let uu____13873 =
        let uu____13874 =
          let uu____13891 =
            let uu____13902 = FStar_Syntax_Syntax.as_arg t  in [uu____13902]
             in
          (reflect_, uu____13891)  in
        FStar_Syntax_Syntax.Tm_app uu____13874  in
      FStar_Syntax_Syntax.mk uu____13873  in
    uu____13866 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13946 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____13971 = unfold_lazy i  in delta_qualifier uu____13971
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____13973 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____13974 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____13975 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____13998 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14011 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14012 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14019 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14020 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14036) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14041;
           FStar_Syntax_Syntax.index = uu____14042;
           FStar_Syntax_Syntax.sort = t2;_},uu____14044)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14053) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14059,uu____14060) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14102) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14127,t2,uu____14129) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14154,t2) -> delta_qualifier t2
  
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
    let uu____14193 = delta_qualifier t  in incr_delta_depth uu____14193
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14201 =
      let uu____14202 = FStar_Syntax_Subst.compress t  in
      uu____14202.FStar_Syntax_Syntax.n  in
    match uu____14201 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14207 -> false
  
let rec apply_last :
  'Auu____14216 .
    ('Auu____14216 -> 'Auu____14216) ->
      'Auu____14216 Prims.list -> 'Auu____14216 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14242 = f a  in [uu____14242]
      | x::xs -> let uu____14247 = apply_last f xs  in x :: uu____14247
  
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
          let uu____14302 =
            let uu____14309 =
              let uu____14310 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14310  in
            FStar_Syntax_Syntax.mk uu____14309  in
          uu____14302 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____14324 =
            let uu____14329 =
              let uu____14330 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14330
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14329 args  in
          uu____14324 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14344 =
            let uu____14349 =
              let uu____14350 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14350
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14349 args  in
          uu____14344 FStar_Pervasives_Native.None pos  in
        let uu____14351 =
          let uu____14352 =
            let uu____14353 = FStar_Syntax_Syntax.iarg typ  in [uu____14353]
             in
          nil uu____14352 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14387 =
                 let uu____14388 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14397 =
                   let uu____14408 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14417 =
                     let uu____14428 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14428]  in
                   uu____14408 :: uu____14417  in
                 uu____14388 :: uu____14397  in
               cons1 uu____14387 t.FStar_Syntax_Syntax.pos) l uu____14351
  
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
        | uu____14537 -> false
  
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
          | uu____14651 -> false
  
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
        | uu____14817 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____14855 = FStar_ST.op_Bang debug_term_eq  in
          if uu____14855
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
        let t11 = let uu____15059 = unmeta_safe t1  in canon_app uu____15059
           in
        let t21 = let uu____15065 = unmeta_safe t2  in canon_app uu____15065
           in
        let uu____15068 =
          let uu____15073 =
            let uu____15074 =
              let uu____15077 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15077  in
            uu____15074.FStar_Syntax_Syntax.n  in
          let uu____15078 =
            let uu____15079 =
              let uu____15082 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15082  in
            uu____15079.FStar_Syntax_Syntax.n  in
          (uu____15073, uu____15078)  in
        match uu____15068 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15084,uu____15085) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15094,FStar_Syntax_Syntax.Tm_uinst uu____15095) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15104,uu____15105) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15130,FStar_Syntax_Syntax.Tm_delayed uu____15131) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15156,uu____15157) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15186,FStar_Syntax_Syntax.Tm_ascribed uu____15187) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15226 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15226
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15231 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15231
        | (FStar_Syntax_Syntax.Tm_type
           uu____15234,FStar_Syntax_Syntax.Tm_type uu____15235) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15293 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15293) &&
              (let uu____15303 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15303)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15352 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15352) &&
              (let uu____15362 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15362)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15379 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15379) &&
              (let uu____15383 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15383)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15440 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15440) &&
              (let uu____15444 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15444)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15533 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15533) &&
              (let uu____15537 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15537)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15554,uu____15555) ->
            let uu____15556 =
              let uu____15558 = unlazy t11  in
              term_eq_dbg dbg uu____15558 t21  in
            check "lazy_l" uu____15556
        | (uu____15560,FStar_Syntax_Syntax.Tm_lazy uu____15561) ->
            let uu____15562 =
              let uu____15564 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15564  in
            check "lazy_r" uu____15562
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15609 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15609))
              &&
              (let uu____15613 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15613)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15617),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15619)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15677 =
               let uu____15679 = eq_quoteinfo qi1 qi2  in uu____15679 = Equal
                in
             check "tm_quoted qi" uu____15677) &&
              (let uu____15682 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15682)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15712 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15712) &&
                   (let uu____15716 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15716)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15735 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15735) &&
                    (let uu____15739 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15739))
                   &&
                   (let uu____15743 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15743)
             | uu____15746 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15752) -> fail "unk"
        | (uu____15754,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15756,uu____15757) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15759,uu____15760) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15762,uu____15763) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15765,uu____15766) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15768,uu____15769) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15771,uu____15772) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15792,uu____15793) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15809,uu____15810) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15818,uu____15819) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15837,uu____15838) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____15862,uu____15863) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____15878,uu____15879) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____15893,uu____15894) ->
            fail "bottom"
        | (uu____15902,FStar_Syntax_Syntax.Tm_bvar uu____15903) ->
            fail "bottom"
        | (uu____15905,FStar_Syntax_Syntax.Tm_name uu____15906) ->
            fail "bottom"
        | (uu____15908,FStar_Syntax_Syntax.Tm_fvar uu____15909) ->
            fail "bottom"
        | (uu____15911,FStar_Syntax_Syntax.Tm_constant uu____15912) ->
            fail "bottom"
        | (uu____15914,FStar_Syntax_Syntax.Tm_type uu____15915) ->
            fail "bottom"
        | (uu____15917,FStar_Syntax_Syntax.Tm_abs uu____15918) ->
            fail "bottom"
        | (uu____15938,FStar_Syntax_Syntax.Tm_arrow uu____15939) ->
            fail "bottom"
        | (uu____15955,FStar_Syntax_Syntax.Tm_refine uu____15956) ->
            fail "bottom"
        | (uu____15964,FStar_Syntax_Syntax.Tm_app uu____15965) ->
            fail "bottom"
        | (uu____15983,FStar_Syntax_Syntax.Tm_match uu____15984) ->
            fail "bottom"
        | (uu____16008,FStar_Syntax_Syntax.Tm_let uu____16009) ->
            fail "bottom"
        | (uu____16024,FStar_Syntax_Syntax.Tm_uvar uu____16025) ->
            fail "bottom"
        | (uu____16039,FStar_Syntax_Syntax.Tm_meta uu____16040) ->
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
               let uu____16075 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16075)
          (fun q1  ->
             fun q2  ->
               let uu____16087 =
                 let uu____16089 = eq_aqual q1 q2  in uu____16089 = Equal  in
               check "arg qual" uu____16087) a1 a2

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
               let uu____16114 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16114)
          (fun q1  ->
             fun q2  ->
               let uu____16126 =
                 let uu____16128 = eq_aqual q1 q2  in uu____16128 = Equal  in
               check "binder qual" uu____16126) b1 b2

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
        ((let uu____16142 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16142) &&
           (let uu____16146 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16146))
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
    fun uu____16156  ->
      fun uu____16157  ->
        match (uu____16156, uu____16157) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16284 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16284) &&
               (let uu____16288 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16288))
              &&
              (let uu____16292 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16334 -> false  in
               check "branch when" uu____16292)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16355 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16355) &&
           (let uu____16364 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16364))
          &&
          (let uu____16368 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16368)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16385 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16385 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16439 ->
        let uu____16462 =
          let uu____16464 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16464  in
        Prims.int_one + uu____16462
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16467 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16467
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16471 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16471
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16480 = sizeof t1  in (FStar_List.length us) + uu____16480
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16484) ->
        let uu____16509 = sizeof t1  in
        let uu____16511 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16526  ->
                 match uu____16526 with
                 | (bv,uu____16536) ->
                     let uu____16541 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16541) Prims.int_zero bs
           in
        uu____16509 + uu____16511
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____16570 = sizeof hd1  in
        let uu____16572 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16587  ->
                 match uu____16587 with
                 | (arg,uu____16597) ->
                     let uu____16602 = sizeof arg  in acc + uu____16602)
            Prims.int_zero args
           in
        uu____16570 + uu____16572
    | uu____16605 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16619 =
        let uu____16620 = un_uinst t  in uu____16620.FStar_Syntax_Syntax.n
         in
      match uu____16619 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16625 -> false
  
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
           let uu____16686 = head_and_args t  in
           match uu____16686 with
           | (head1,args) ->
               let uu____16741 =
                 let uu____16742 = FStar_Syntax_Subst.compress head1  in
                 uu____16742.FStar_Syntax_Syntax.n  in
               (match uu____16741 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16768 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____16801 = is_fvar attr a  in Prims.op_Negation uu____16801)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options1 s =
        let uu____16822 = FStar_Options.set_options s  in
        match uu____16822 with
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
          ((let uu____16836 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16836 (fun a1  -> ()));
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
          let uu____16851 = FStar_Options.internal_pop ()  in
          if uu____16851
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
    | FStar_Syntax_Syntax.Tm_delayed uu____16883 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____16910 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____16925 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____16926 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____16927 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16936) ->
        let uu____16961 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____16961 with
         | (bs1,t2) ->
             let uu____16970 =
               FStar_List.collect
                 (fun uu____16982  ->
                    match uu____16982 with
                    | (b,uu____16992) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____16997 = unbound_variables t2  in
             FStar_List.append uu____16970 uu____16997)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17022 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17022 with
         | (bs1,c1) ->
             let uu____17031 =
               FStar_List.collect
                 (fun uu____17043  ->
                    match uu____17043 with
                    | (b,uu____17053) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17058 = unbound_variables_comp c1  in
             FStar_List.append uu____17031 uu____17058)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17067 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17067 with
         | (bs,t2) ->
             let uu____17090 =
               FStar_List.collect
                 (fun uu____17102  ->
                    match uu____17102 with
                    | (b1,uu____17112) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17117 = unbound_variables t2  in
             FStar_List.append uu____17090 uu____17117)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17146 =
          FStar_List.collect
            (fun uu____17160  ->
               match uu____17160 with
               | (x,uu____17172) -> unbound_variables x) args
           in
        let uu____17181 = unbound_variables t1  in
        FStar_List.append uu____17146 uu____17181
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17222 = unbound_variables t1  in
        let uu____17225 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17240 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17240 with
                  | (p,wopt,t2) ->
                      let uu____17262 = unbound_variables t2  in
                      let uu____17265 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17262 uu____17265))
           in
        FStar_List.append uu____17222 uu____17225
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17279) ->
        let uu____17320 = unbound_variables t1  in
        let uu____17323 =
          let uu____17326 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17357 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17326 uu____17357  in
        FStar_List.append uu____17320 uu____17323
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17398 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17401 =
          let uu____17404 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17407 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17412 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17414 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17414 with
                 | (uu____17435,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17404 uu____17407  in
        FStar_List.append uu____17398 uu____17401
    | FStar_Syntax_Syntax.Tm_let ((uu____17437,lbs),t1) ->
        let uu____17457 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17457 with
         | (lbs1,t2) ->
             let uu____17472 = unbound_variables t2  in
             let uu____17475 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17482 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17485 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17482 uu____17485) lbs1
                in
             FStar_List.append uu____17472 uu____17475)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17502 = unbound_variables t1  in
        let uu____17505 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17510,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17565  ->
                      match uu____17565 with
                      | (a,uu____17577) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17586,uu____17587,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17593,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17599 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17608 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17609 -> []  in
        FStar_List.append uu____17502 uu____17505

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17616) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17626) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17636 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17639 =
          FStar_List.collect
            (fun uu____17653  ->
               match uu____17653 with
               | (a,uu____17665) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17636 uu____17639

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
            let uu____17780 = head_and_args h  in
            (match uu____17780 with
             | (head1,args) ->
                 let uu____17841 =
                   let uu____17842 = FStar_Syntax_Subst.compress head1  in
                   uu____17842.FStar_Syntax_Syntax.n  in
                 (match uu____17841 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____17895 -> aux (h :: acc) t))
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
      let uu____17919 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____17919 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2464_17961 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2464_17961.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2464_17961.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2464_17961.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2464_17961.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2464_17961.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____17969 =
      let uu____17970 = FStar_Syntax_Subst.compress t  in
      uu____17970.FStar_Syntax_Syntax.n  in
    match uu____17969 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____17974,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18002)::uu____18003 ->
                  let pats' = unmeta pats  in
                  let uu____18063 = head_and_args pats'  in
                  (match uu____18063 with
                   | (head1,uu____18082) ->
                       let uu____18107 =
                         let uu____18108 = un_uinst head1  in
                         uu____18108.FStar_Syntax_Syntax.n  in
                       (match uu____18107 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18113 -> false))
              | uu____18115 -> false)
         | uu____18127 -> false)
    | uu____18129 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18145 =
      let uu____18162 = unmeta e  in head_and_args uu____18162  in
    match uu____18145 with
    | (head1,args) ->
        let uu____18193 =
          let uu____18208 =
            let uu____18209 = un_uinst head1  in
            uu____18209.FStar_Syntax_Syntax.n  in
          (uu____18208, args)  in
        (match uu____18193 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18227) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18251::(hd1,uu____18253)::(tl1,uu____18255)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18322 =
               let uu____18325 =
                 let uu____18328 = list_elements tl1  in
                 FStar_Util.must uu____18328  in
               hd1 :: uu____18325  in
             FStar_Pervasives_Native.Some uu____18322
         | uu____18337 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18366 =
      let uu____18367 = FStar_Syntax_Subst.compress t  in
      uu____18367.FStar_Syntax_Syntax.n  in
    match uu____18366 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18374) ->
        let uu____18409 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18409 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18443 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18443
             then
               let uu____18450 =
                 let uu____18461 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18461]  in
               mk_app t uu____18450
             else e1)
    | uu____18488 ->
        let uu____18489 =
          let uu____18500 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18500]  in
        mk_app t uu____18489
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18555 = list_elements e  in
        match uu____18555 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18590 =
          let uu____18607 = unmeta p  in
          FStar_All.pipe_right uu____18607 head_and_args  in
        match uu____18590 with
        | (head1,args) ->
            let uu____18658 =
              let uu____18673 =
                let uu____18674 = un_uinst head1  in
                uu____18674.FStar_Syntax_Syntax.n  in
              (uu____18673, args)  in
            (match uu____18658 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18696,uu____18697)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18749 ->
                 let uu____18764 =
                   let uu____18770 =
                     let uu____18772 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18772
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____18770)  in
                 FStar_Errors.raise_error uu____18764
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____18815 =
            let uu____18832 = unmeta t1  in
            FStar_All.pipe_right uu____18832 head_and_args  in
          match uu____18815 with
          | (head1,args) ->
              let uu____18879 =
                let uu____18894 =
                  let uu____18895 = un_uinst head1  in
                  uu____18895.FStar_Syntax_Syntax.n  in
                (uu____18894, args)  in
              (match uu____18879 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____18914)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____18951 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____18981 = smt_pat_or1 t1  in
            (match uu____18981 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19003 = list_elements1 e  in
                 FStar_All.pipe_right uu____19003
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19033 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19033
                           (FStar_List.map one_pat)))
             | uu____19062 ->
                 let uu____19067 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19067])
        | uu____19122 ->
            let uu____19125 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19125]
         in
      let uu____19180 =
        let uu____19213 =
          let uu____19214 = FStar_Syntax_Subst.compress t  in
          uu____19214.FStar_Syntax_Syntax.n  in
        match uu____19213 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19271 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19271 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19342;
                        FStar_Syntax_Syntax.effect_name = uu____19343;
                        FStar_Syntax_Syntax.result_typ = uu____19344;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19346)::(post,uu____19348)::(pats,uu____19350)::[];
                        FStar_Syntax_Syntax.flags = uu____19351;_}
                      ->
                      let uu____19412 = lemma_pats pats  in
                      (binders1, pre, post, uu____19412)
                  | uu____19449 -> failwith "impos"))
        | uu____19483 -> failwith "Impos"  in
      match uu____19180 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19575 =
              let uu____19582 =
                let uu____19583 =
                  let uu____19590 = mk_imp pre post1  in
                  let uu____19593 =
                    let uu____19594 =
                      let uu____19615 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19615, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19594  in
                  (uu____19590, uu____19593)  in
                FStar_Syntax_Syntax.Tm_meta uu____19583  in
              FStar_Syntax_Syntax.mk uu____19582  in
            uu____19575 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19639 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19639 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19669 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19680 -> true
    | uu____19682 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19693 -> true
    | uu____19695 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19713 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19714 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19715 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19716 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19717 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19718 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19719 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19720 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19723 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19726 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19713;
        FStar_Syntax_Syntax.bind_wp = uu____19714;
        FStar_Syntax_Syntax.stronger = uu____19715;
        FStar_Syntax_Syntax.if_then_else = uu____19716;
        FStar_Syntax_Syntax.ite_wp = uu____19717;
        FStar_Syntax_Syntax.close_wp = uu____19718;
        FStar_Syntax_Syntax.trivial = uu____19719;
        FStar_Syntax_Syntax.repr = uu____19720;
        FStar_Syntax_Syntax.return_repr = uu____19723;
        FStar_Syntax_Syntax.bind_repr = uu____19726
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____19758 =
        match uu____19758 with
        | (ts1,ts2) ->
            let uu____19769 = f ts1  in
            let uu____19770 = f ts2  in (uu____19769, uu____19770)
         in
      let uu____19771 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____19776 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____19781 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____19786 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____19791 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____19771;
        FStar_Syntax_Syntax.l_return = uu____19776;
        FStar_Syntax_Syntax.l_bind = uu____19781;
        FStar_Syntax_Syntax.l_subcomp = uu____19786;
        FStar_Syntax_Syntax.l_if_then_else = uu____19791
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
          let uu____19813 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____19813
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19815 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____19815
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19817 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____19817
  
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
    | uu____19832 -> FStar_Pervasives_Native.None
  
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
        let uu____19846 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19846
          (fun _19853  -> FStar_Pervasives_Native.Some _19853)
  
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
        let uu____19893 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19893
          (fun _19900  -> FStar_Pervasives_Native.Some _19900)
  
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
        let uu____19914 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19914
          (fun _19921  -> FStar_Pervasives_Native.Some _19921)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun _19935  -> FStar_Pervasives_Native.Some _19935)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun _19939  -> FStar_Pervasives_Native.Some _19939)
    | uu____19940 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19952 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19952
          (fun _19959  -> FStar_Pervasives_Native.Some _19959)
    | uu____19960 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun _19974  -> FStar_Pervasives_Native.Some _19974)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun _19978  -> FStar_Pervasives_Native.Some _19978)
    | uu____19979 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun _19993  -> FStar_Pervasives_Native.Some _19993)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun _19997  -> FStar_Pervasives_Native.Some _19997)
    | uu____19998 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20022 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20023 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20025 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20025
          (fun _20032  -> FStar_Pervasives_Native.Some _20032)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun _20046  -> FStar_Pervasives_Native.Some _20046)
    | uu____20047 -> FStar_Pervasives_Native.None
  