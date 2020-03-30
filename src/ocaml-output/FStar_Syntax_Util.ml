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
    | FStar_Syntax_Syntax.Sig_fail uu____5351 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5364 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    let uu____5385 = lids_of_sigelt se  in
    match uu____5385 with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5391 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5417  ->
    match uu___7_5417 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____5431 'Auu____5432 .
    ('Auu____5431 FStar_Syntax_Syntax.syntax * 'Auu____5432) ->
      FStar_Range.range
  =
  fun uu____5443  ->
    match uu____5443 with | (hd1,uu____5451) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5465 'Auu____5466 .
    ('Auu____5465 FStar_Syntax_Syntax.syntax * 'Auu____5466) Prims.list ->
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
      | uu____5564 ->
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
      let uu____5623 =
        FStar_List.map
          (fun uu____5650  ->
             match uu____5650 with
             | (bv,aq) ->
                 let uu____5669 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5669, aq)) bs
         in
      mk_app f uu____5623
  
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
          let uu____5744 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5744
          then
            let uu____5747 =
              let uu____5753 =
                let uu____5755 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5755  in
              let uu____5758 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5753, uu____5758)  in
            FStar_Ident.mk_ident uu____5747
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___940_5763 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___940_5763.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___940_5763.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5764 = mk_field_projector_name_from_ident lid nm  in
        (uu____5764, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5776) -> ses
    | uu____5785 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5800 = FStar_Syntax_Unionfind.find uv  in
      match uu____5800 with
      | FStar_Pervasives_Native.Some uu____5803 ->
          let uu____5804 =
            let uu____5806 =
              let uu____5808 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5808  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5806  in
          failwith uu____5804
      | uu____5813 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____5896 -> q1 = q2
  
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
              let uu____5942 =
                let uu___997_5943 = rc  in
                let uu____5944 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___997_5943.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____5944;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___997_5943.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____5942
           in
        match bs with
        | [] -> t
        | uu____5961 ->
            let body =
              let uu____5963 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____5963  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____5993 =
                   let uu____6000 =
                     let uu____6001 =
                       let uu____6020 =
                         let uu____6029 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6029 bs'  in
                       let uu____6044 = close_lopt lopt'  in
                       (uu____6020, t1, uu____6044)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6001  in
                   FStar_Syntax_Syntax.mk uu____6000  in
                 uu____5993 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6059 ->
                 let uu____6060 =
                   let uu____6067 =
                     let uu____6068 =
                       let uu____6087 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6096 = close_lopt lopt  in
                       (uu____6087, body, uu____6096)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6068  in
                   FStar_Syntax_Syntax.mk uu____6067  in
                 uu____6060 FStar_Pervasives_Native.None
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
      | uu____6152 ->
          let uu____6161 =
            let uu____6168 =
              let uu____6169 =
                let uu____6184 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6193 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6184, uu____6193)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6169  in
            FStar_Syntax_Syntax.mk uu____6168  in
          uu____6161 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6242 =
        let uu____6243 = FStar_Syntax_Subst.compress t  in
        uu____6243.FStar_Syntax_Syntax.n  in
      match uu____6242 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6273) ->
               let uu____6282 =
                 let uu____6283 = FStar_Syntax_Subst.compress tres  in
                 uu____6283.FStar_Syntax_Syntax.n  in
               (match uu____6282 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6326 -> t)
           | uu____6327 -> t)
      | uu____6328 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6346 =
        let uu____6347 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6347 t.FStar_Syntax_Syntax.pos  in
      let uu____6348 =
        let uu____6355 =
          let uu____6356 =
            let uu____6363 =
              let uu____6366 =
                let uu____6367 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6367]  in
              FStar_Syntax_Subst.close uu____6366 t  in
            (b, uu____6363)  in
          FStar_Syntax_Syntax.Tm_refine uu____6356  in
        FStar_Syntax_Syntax.mk uu____6355  in
      uu____6348 FStar_Pervasives_Native.None uu____6346
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec (arrow_formals_comp_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____6447 = is_total_comp c  in
        if uu____6447
        then
          let uu____6462 = arrow_formals_comp_ln (comp_result c)  in
          (match uu____6462 with
           | (bs',k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6529;
           FStar_Syntax_Syntax.index = uu____6530;
           FStar_Syntax_Syntax.sort = s;_},uu____6532)
        ->
        let rec aux s1 k2 =
          let uu____6563 =
            let uu____6564 = FStar_Syntax_Subst.compress s1  in
            uu____6564.FStar_Syntax_Syntax.n  in
          match uu____6563 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6579 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6594;
                 FStar_Syntax_Syntax.index = uu____6595;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6597)
              -> aux s2 k2
          | uu____6605 ->
              let uu____6606 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6606)
           in
        aux s k1
    | uu____6621 ->
        let uu____6622 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6622)
  
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let uu____6647 = arrow_formals_comp_ln k  in
    match uu____6647 with | (bs,c) -> FStar_Syntax_Subst.open_comp bs c
  
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6702 = arrow_formals_comp_ln k  in
    match uu____6702 with | (bs,c) -> (bs, (comp_result c))
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6769 = arrow_formals_comp k  in
    match uu____6769 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6871 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6871 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6895 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_6904  ->
                         match uu___8_6904 with
                         | FStar_Syntax_Syntax.DECREASES uu____6906 -> true
                         | uu____6910 -> false))
                  in
               (match uu____6895 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____6945 ->
                    let uu____6948 = is_total_comp c1  in
                    if uu____6948
                    then
                      let uu____6967 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____6967 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7060;
             FStar_Syntax_Syntax.index = uu____7061;
             FStar_Syntax_Syntax.sort = k2;_},uu____7063)
          -> arrow_until_decreases k2
      | uu____7071 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7092 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7092 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7146 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7167 =
                 FStar_Common.tabulate n_univs (fun uu____7173  -> false)  in
               let uu____7176 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7201  ->
                         match uu____7201 with
                         | (x,uu____7210) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7167 uu____7176)
           in
        ((n_univs + (FStar_List.length bs)), uu____7146)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7266 =
            let uu___1124_7267 = rc  in
            let uu____7268 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1124_7267.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7268;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1124_7267.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7266
      | uu____7277 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7311 =
        let uu____7312 =
          let uu____7315 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7315  in
        uu____7312.FStar_Syntax_Syntax.n  in
      match uu____7311 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7361 = aux t2 what  in
          (match uu____7361 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7433 -> ([], t1, abs_body_lcomp)  in
    let uu____7450 = aux t FStar_Pervasives_Native.None  in
    match uu____7450 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7498 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7498 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let no_acc uu____7532 =
      match uu____7532 with
      | (b,aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true )) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7546 -> aq  in
          (b, aq1)
       in
    let uu____7551 = arrow_formals_comp_ln t  in
    match uu____7551 with
    | (bs,c) ->
        (match bs with
         | [] -> t
         | uu____7588 ->
             let uu____7597 =
               let uu____7604 =
                 let uu____7605 =
                   let uu____7620 = FStar_List.map no_acc bs  in
                   (uu____7620, c)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____7605  in
               FStar_Syntax_Syntax.mk uu____7604  in
             uu____7597 FStar_Pervasives_Native.None
               t.FStar_Syntax_Syntax.pos)
  
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
                    | (FStar_Pervasives_Native.None ,uu____7791) -> def
                    | (uu____7802,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7814) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _7830  ->
                                  FStar_Syntax_Syntax.U_name _7830))
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
            let uu____7912 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7912 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7947 ->
            let t' = arrow binders c  in
            let uu____7959 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____7959 with
             | (uvs1,t'1) ->
                 let uu____7980 =
                   let uu____7981 = FStar_Syntax_Subst.compress t'1  in
                   uu____7981.FStar_Syntax_Syntax.n  in
                 (match uu____7980 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8030 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____8055 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8066 -> false
  
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
      let uu____8129 =
        let uu____8130 = pre_typ t  in uu____8130.FStar_Syntax_Syntax.n  in
      match uu____8129 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8135 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8149 =
        let uu____8150 = pre_typ t  in uu____8150.FStar_Syntax_Syntax.n  in
      match uu____8149 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8154 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8156) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8182) ->
          is_constructed_typ t1 lid
      | uu____8187 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8200 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8201 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8202 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8204) -> get_tycon t2
    | uu____8229 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8237 =
      let uu____8238 = un_uinst t  in uu____8238.FStar_Syntax_Syntax.n  in
    match uu____8237 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8243 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8257 =
        let uu____8261 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8261  in
      match uu____8257 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8293 -> false
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
  fun uu____8312  ->
    let u =
      let uu____8318 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _8335  -> FStar_Syntax_Syntax.U_unif _8335)
        uu____8318
       in
    let uu____8336 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8336, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8349 = eq_tm a a'  in
      match uu____8349 with | Equal  -> true | uu____8352 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8357 =
    let uu____8364 =
      let uu____8365 =
        let uu____8366 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8366
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8365  in
    FStar_Syntax_Syntax.mk uu____8364  in
  uu____8357 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8479 =
            let uu____8482 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8483 =
              let uu____8490 =
                let uu____8491 =
                  let uu____8508 =
                    let uu____8519 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8528 =
                      let uu____8539 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8539]  in
                    uu____8519 :: uu____8528  in
                  (tand, uu____8508)  in
                FStar_Syntax_Syntax.Tm_app uu____8491  in
              FStar_Syntax_Syntax.mk uu____8490  in
            uu____8483 FStar_Pervasives_Native.None uu____8482  in
          FStar_Pervasives_Native.Some uu____8479
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8616 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8617 =
          let uu____8624 =
            let uu____8625 =
              let uu____8642 =
                let uu____8653 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8662 =
                  let uu____8673 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8673]  in
                uu____8653 :: uu____8662  in
              (op_t, uu____8642)  in
            FStar_Syntax_Syntax.Tm_app uu____8625  in
          FStar_Syntax_Syntax.mk uu____8624  in
        uu____8617 FStar_Pervasives_Native.None uu____8616
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8730 =
      let uu____8737 =
        let uu____8738 =
          let uu____8755 =
            let uu____8766 = FStar_Syntax_Syntax.as_arg phi  in [uu____8766]
             in
          (t_not, uu____8755)  in
        FStar_Syntax_Syntax.Tm_app uu____8738  in
      FStar_Syntax_Syntax.mk uu____8737  in
    uu____8730 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____8963 =
      let uu____8970 =
        let uu____8971 =
          let uu____8988 =
            let uu____8999 = FStar_Syntax_Syntax.as_arg e  in [uu____8999]
             in
          (b2t_v, uu____8988)  in
        FStar_Syntax_Syntax.Tm_app uu____8971  in
      FStar_Syntax_Syntax.mk uu____8970  in
    uu____8963 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9046 = head_and_args e  in
    match uu____9046 with
    | (hd1,args) ->
        let uu____9091 =
          let uu____9106 =
            let uu____9107 = FStar_Syntax_Subst.compress hd1  in
            uu____9107.FStar_Syntax_Syntax.n  in
          (uu____9106, args)  in
        (match uu____9091 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9124)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9159 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9181 =
      let uu____9182 = unmeta t  in uu____9182.FStar_Syntax_Syntax.n  in
    match uu____9181 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9187 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9210 = is_t_true t1  in
      if uu____9210
      then t2
      else
        (let uu____9217 = is_t_true t2  in
         if uu____9217 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9245 = is_t_true t1  in
      if uu____9245
      then t_true
      else
        (let uu____9252 = is_t_true t2  in
         if uu____9252 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9281 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9282 =
        let uu____9289 =
          let uu____9290 =
            let uu____9307 =
              let uu____9318 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9327 =
                let uu____9338 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9338]  in
              uu____9318 :: uu____9327  in
            (teq, uu____9307)  in
          FStar_Syntax_Syntax.Tm_app uu____9290  in
        FStar_Syntax_Syntax.mk uu____9289  in
      uu____9282 FStar_Pervasives_Native.None uu____9281
  
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
          let uu____9405 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9406 =
            let uu____9413 =
              let uu____9414 =
                let uu____9431 =
                  let uu____9442 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9451 =
                    let uu____9462 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9471 =
                      let uu____9482 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9482]  in
                    uu____9462 :: uu____9471  in
                  uu____9442 :: uu____9451  in
                (eq_inst, uu____9431)  in
              FStar_Syntax_Syntax.Tm_app uu____9414  in
            FStar_Syntax_Syntax.mk uu____9413  in
          uu____9406 FStar_Pervasives_Native.None uu____9405
  
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
        let uu____9559 =
          let uu____9566 =
            let uu____9567 =
              let uu____9584 =
                let uu____9595 = FStar_Syntax_Syntax.iarg t  in
                let uu____9604 =
                  let uu____9615 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9624 =
                    let uu____9635 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9635]  in
                  uu____9615 :: uu____9624  in
                uu____9595 :: uu____9604  in
              (t_has_type1, uu____9584)  in
            FStar_Syntax_Syntax.Tm_app uu____9567  in
          FStar_Syntax_Syntax.mk uu____9566  in
        uu____9559 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9712 =
          let uu____9719 =
            let uu____9720 =
              let uu____9737 =
                let uu____9748 = FStar_Syntax_Syntax.iarg t  in
                let uu____9757 =
                  let uu____9768 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9768]  in
                uu____9748 :: uu____9757  in
              (t_with_type1, uu____9737)  in
            FStar_Syntax_Syntax.Tm_app uu____9720  in
          FStar_Syntax_Syntax.mk uu____9719  in
        uu____9712 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9815 =
    let uu____9822 =
      let uu____9823 =
        let uu____9830 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9830, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9823  in
    FStar_Syntax_Syntax.mk uu____9822  in
  uu____9815 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
        let uu____9913 =
          let uu____9920 =
            let uu____9921 =
              let uu____9938 =
                let uu____9949 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____9958 =
                  let uu____9969 =
                    let uu____9978 =
                      let uu____9979 =
                        let uu____9980 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____9980]  in
                      abs uu____9979 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____9978  in
                  [uu____9969]  in
                uu____9949 :: uu____9958  in
              (fa, uu____9938)  in
            FStar_Syntax_Syntax.Tm_app uu____9921  in
          FStar_Syntax_Syntax.mk uu____9920  in
        uu____9913 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10107 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10107
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10126 -> true
    | uu____10128 -> false
  
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
          let uu____10175 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10175, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10204 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10204, FStar_Pervasives_Native.None, t2)  in
        let uu____10218 =
          let uu____10219 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10219  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10218
  
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
      let uu____10295 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10298 =
        let uu____10309 = FStar_Syntax_Syntax.as_arg p  in [uu____10309]  in
      mk_app uu____10295 uu____10298
  
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
      let uu____10349 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10352 =
        let uu____10363 = FStar_Syntax_Syntax.as_arg p  in [uu____10363]  in
      mk_app uu____10349 uu____10352
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10398 = head_and_args t  in
    match uu____10398 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____10447 =
          let uu____10462 =
            let uu____10463 = FStar_Syntax_Subst.compress head3  in
            uu____10463.FStar_Syntax_Syntax.n  in
          (uu____10462, args)  in
        (match uu____10447 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10482)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10548 =
                    let uu____10553 =
                      let uu____10554 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10554]  in
                    FStar_Syntax_Subst.open_term uu____10553 p  in
                  (match uu____10548 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10611 -> failwith "impossible"  in
                       let uu____10619 =
                         let uu____10621 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10621
                          in
                       if uu____10619
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10637 -> FStar_Pervasives_Native.None)
         | uu____10640 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10671 = head_and_args t  in
    match uu____10671 with
    | (head1,args) ->
        let uu____10722 =
          let uu____10737 =
            let uu____10738 = FStar_Syntax_Subst.compress head1  in
            uu____10738.FStar_Syntax_Syntax.n  in
          (uu____10737, args)  in
        (match uu____10722 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10760;
               FStar_Syntax_Syntax.vars = uu____10761;_},u::[]),(t1,uu____10764)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10811 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10846 = head_and_args t  in
    match uu____10846 with
    | (head1,args) ->
        let uu____10897 =
          let uu____10912 =
            let uu____10913 = FStar_Syntax_Subst.compress head1  in
            uu____10913.FStar_Syntax_Syntax.n  in
          (uu____10912, args)  in
        (match uu____10897 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10935;
               FStar_Syntax_Syntax.vars = uu____10936;_},u::[]),(t1,uu____10939)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10986 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11014 =
      let uu____11031 = unmeta t  in head_and_args uu____11031  in
    match uu____11014 with
    | (head1,uu____11034) ->
        let uu____11059 =
          let uu____11060 = un_uinst head1  in
          uu____11060.FStar_Syntax_Syntax.n  in
        (match uu____11059 with
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
         | uu____11065 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11085 =
      let uu____11086 = FStar_Syntax_Subst.compress t  in
      uu____11086.FStar_Syntax_Syntax.n  in
    match uu____11085 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11192 =
          let uu____11197 =
            let uu____11198 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11198  in
          (b, uu____11197)  in
        FStar_Pervasives_Native.Some uu____11192
    | uu____11203 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11226 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11226
      (fun uu____11254  ->
         match uu____11254 with
         | (b,c) ->
             let uu____11273 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11273 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11336 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11373 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11373
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11425 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11468 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11509 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11895) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11907) ->
          unmeta_monadic t
      | uu____11920 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____11989 =
        match uu____11989 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12027  ->
                   match uu____12027 with
                   | (lid,out_lid) ->
                       let uu____12036 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12036
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12063 = head_and_args t  in
      match uu____12063 with
      | (hd1,args) ->
          let uu____12108 =
            let uu____12109 = un_uinst hd1  in
            uu____12109.FStar_Syntax_Syntax.n  in
          (match uu____12108 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12115 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12124 = un_squash t  in
      FStar_Util.bind_opt uu____12124
        (fun t1  ->
           let uu____12140 = head_and_args' t1  in
           match uu____12140 with
           | (hd1,args) ->
               let uu____12179 =
                 let uu____12180 = un_uinst hd1  in
                 uu____12180.FStar_Syntax_Syntax.n  in
               (match uu____12179 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12186 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12227,pats)) ->
          let uu____12265 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12265)
      | uu____12278 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12345 = head_and_args t1  in
        match uu____12345 with
        | (t2,args) ->
            let uu____12400 = un_uinst t2  in
            let uu____12401 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12442  ->
                      match uu____12442 with
                      | (t3,imp) ->
                          let uu____12461 = unascribe t3  in
                          (uu____12461, imp)))
               in
            (uu____12400, uu____12401)
         in
      let rec aux qopt out t1 =
        let uu____12512 = let uu____12536 = flat t1  in (qopt, uu____12536)
           in
        match uu____12512 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12576;
                 FStar_Syntax_Syntax.vars = uu____12577;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12580);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12581;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12582;_},uu____12583)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12685;
                 FStar_Syntax_Syntax.vars = uu____12686;_},uu____12687::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12690);
                  FStar_Syntax_Syntax.pos = uu____12691;
                  FStar_Syntax_Syntax.vars = uu____12692;_},uu____12693)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12810;
               FStar_Syntax_Syntax.vars = uu____12811;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12814);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12815;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12816;_},uu____12817)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12910 =
              let uu____12914 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12914  in
            aux uu____12910 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12924;
               FStar_Syntax_Syntax.vars = uu____12925;_},uu____12926::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12929);
                FStar_Syntax_Syntax.pos = uu____12930;
                FStar_Syntax_Syntax.vars = uu____12931;_},uu____12932)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13041 =
              let uu____13045 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13045  in
            aux uu____13041 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13055) ->
            let bs = FStar_List.rev out  in
            let uu____13108 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13108 with
             | (bs1,t2) ->
                 let uu____13117 = patterns t2  in
                 (match uu____13117 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13167 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13222 = un_squash t  in
      FStar_Util.bind_opt uu____13222
        (fun t1  ->
           let uu____13237 = arrow_one t1  in
           match uu____13237 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13252 =
                 let uu____13254 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13254  in
               if uu____13252
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13264 = comp_to_comp_typ_nouniv c  in
                    uu____13264.FStar_Syntax_Syntax.result_typ  in
                  let uu____13265 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13265
                  then
                    let uu____13272 = patterns q  in
                    match uu____13272 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13335 =
                       let uu____13336 =
                         let uu____13341 =
                           let uu____13342 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13353 =
                             let uu____13364 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13364]  in
                           uu____13342 :: uu____13353  in
                         (FStar_Parser_Const.imp_lid, uu____13341)  in
                       BaseConn uu____13336  in
                     FStar_Pervasives_Native.Some uu____13335))
           | uu____13397 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13405 = un_squash t  in
      FStar_Util.bind_opt uu____13405
        (fun t1  ->
           let uu____13436 = head_and_args' t1  in
           match uu____13436 with
           | (hd1,args) ->
               let uu____13475 =
                 let uu____13490 =
                   let uu____13491 = un_uinst hd1  in
                   uu____13491.FStar_Syntax_Syntax.n  in
                 (uu____13490, args)  in
               (match uu____13475 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13508)::(a2,uu____13510)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13561 =
                      let uu____13562 = FStar_Syntax_Subst.compress a2  in
                      uu____13562.FStar_Syntax_Syntax.n  in
                    (match uu____13561 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13569) ->
                         let uu____13604 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13604 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13657 -> failwith "impossible"  in
                              let uu____13665 = patterns q1  in
                              (match uu____13665 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13726 -> FStar_Pervasives_Native.None)
                | uu____13727 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13750 = destruct_sq_forall phi  in
          (match uu____13750 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13760  -> FStar_Pervasives_Native.Some _13760)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13767 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13773 = destruct_sq_exists phi  in
          (match uu____13773 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13783  -> FStar_Pervasives_Native.Some _13783)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13790 -> f1)
      | uu____13793 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13797 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13797
      (fun uu____13802  ->
         let uu____13803 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13803
           (fun uu____13808  ->
              let uu____13809 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13809
                (fun uu____13814  ->
                   let uu____13815 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13815
                     (fun uu____13820  ->
                        let uu____13821 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13821
                          (fun uu____13825  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13843 =
            let uu____13848 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13848  in
          let uu____13849 =
            let uu____13850 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13850  in
          let uu____13853 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13843 a.FStar_Syntax_Syntax.action_univs uu____13849
            FStar_Parser_Const.effect_Tot_lid uu____13853 [] pos
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
    let uu____13879 =
      let uu____13886 =
        let uu____13887 =
          let uu____13904 =
            let uu____13915 = FStar_Syntax_Syntax.as_arg t  in [uu____13915]
             in
          (reify_1, uu____13904)  in
        FStar_Syntax_Syntax.Tm_app uu____13887  in
      FStar_Syntax_Syntax.mk uu____13886  in
    uu____13879 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____13967 =
        let uu____13974 =
          let uu____13975 =
            let uu____13976 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____13976  in
          FStar_Syntax_Syntax.Tm_constant uu____13975  in
        FStar_Syntax_Syntax.mk uu____13974  in
      uu____13967 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____13978 =
      let uu____13985 =
        let uu____13986 =
          let uu____14003 =
            let uu____14014 = FStar_Syntax_Syntax.as_arg t  in [uu____14014]
             in
          (reflect_, uu____14003)  in
        FStar_Syntax_Syntax.Tm_app uu____13986  in
      FStar_Syntax_Syntax.mk uu____13985  in
    uu____13978 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14058 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14075 = unfold_lazy i  in delta_qualifier uu____14075
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14077 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14078 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14079 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14102 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14115 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14116 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14123 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14124 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14140) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14145;
           FStar_Syntax_Syntax.index = uu____14146;
           FStar_Syntax_Syntax.sort = t2;_},uu____14148)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14157) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14163,uu____14164) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14206) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14231,t2,uu____14233) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14258,t2) -> delta_qualifier t2
  
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
    let uu____14297 = delta_qualifier t  in incr_delta_depth uu____14297
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14305 =
      let uu____14306 = FStar_Syntax_Subst.compress t  in
      uu____14306.FStar_Syntax_Syntax.n  in
    match uu____14305 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14311 -> false
  
let rec apply_last :
  'Auu____14320 .
    ('Auu____14320 -> 'Auu____14320) ->
      'Auu____14320 Prims.list -> 'Auu____14320 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14346 = f a  in [uu____14346]
      | x::xs -> let uu____14351 = apply_last f xs  in x :: uu____14351
  
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
          let uu____14406 =
            let uu____14413 =
              let uu____14414 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14414  in
            FStar_Syntax_Syntax.mk uu____14413  in
          uu____14406 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____14428 =
            let uu____14433 =
              let uu____14434 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14434
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14433 args  in
          uu____14428 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14448 =
            let uu____14453 =
              let uu____14454 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14454
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14453 args  in
          uu____14448 FStar_Pervasives_Native.None pos  in
        let uu____14455 =
          let uu____14456 =
            let uu____14457 = FStar_Syntax_Syntax.iarg typ  in [uu____14457]
             in
          nil uu____14456 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14491 =
                 let uu____14492 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14501 =
                   let uu____14512 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14521 =
                     let uu____14532 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14532]  in
                   uu____14512 :: uu____14521  in
                 uu____14492 :: uu____14501  in
               cons1 uu____14491 t.FStar_Syntax_Syntax.pos) l uu____14455
  
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
        | uu____14641 -> false
  
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
          | uu____14755 -> false
  
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
        | uu____14921 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____14959 = FStar_ST.op_Bang debug_term_eq  in
          if uu____14959
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
        let t11 = let uu____15163 = unmeta_safe t1  in canon_app uu____15163
           in
        let t21 = let uu____15169 = unmeta_safe t2  in canon_app uu____15169
           in
        let uu____15172 =
          let uu____15177 =
            let uu____15178 =
              let uu____15181 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15181  in
            uu____15178.FStar_Syntax_Syntax.n  in
          let uu____15182 =
            let uu____15183 =
              let uu____15186 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15186  in
            uu____15183.FStar_Syntax_Syntax.n  in
          (uu____15177, uu____15182)  in
        match uu____15172 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15188,uu____15189) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15198,FStar_Syntax_Syntax.Tm_uinst uu____15199) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15208,uu____15209) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15226,FStar_Syntax_Syntax.Tm_delayed uu____15227) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15244,uu____15245) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15274,FStar_Syntax_Syntax.Tm_ascribed uu____15275) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15314 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15314
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15319 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15319
        | (FStar_Syntax_Syntax.Tm_type
           uu____15322,FStar_Syntax_Syntax.Tm_type uu____15323) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15381 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15381) &&
              (let uu____15391 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15391)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15440 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15440) &&
              (let uu____15450 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15450)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15467 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15467) &&
              (let uu____15471 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15471)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15528 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15528) &&
              (let uu____15532 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15532)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15621 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15621) &&
              (let uu____15625 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15625)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15642,uu____15643) ->
            let uu____15644 =
              let uu____15646 = unlazy t11  in
              term_eq_dbg dbg uu____15646 t21  in
            check "lazy_l" uu____15644
        | (uu____15648,FStar_Syntax_Syntax.Tm_lazy uu____15649) ->
            let uu____15650 =
              let uu____15652 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15652  in
            check "lazy_r" uu____15650
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15697 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15697))
              &&
              (let uu____15701 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15701)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15705),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15707)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15765 =
               let uu____15767 = eq_quoteinfo qi1 qi2  in uu____15767 = Equal
                in
             check "tm_quoted qi" uu____15765) &&
              (let uu____15770 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15770)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15800 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15800) &&
                   (let uu____15804 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15804)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15823 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15823) &&
                    (let uu____15827 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15827))
                   &&
                   (let uu____15831 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15831)
             | uu____15834 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15840) -> fail "unk"
        | (uu____15842,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15844,uu____15845) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15847,uu____15848) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15850,uu____15851) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15853,uu____15854) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15856,uu____15857) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15859,uu____15860) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15880,uu____15881) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15897,uu____15898) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15906,uu____15907) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15925,uu____15926) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____15950,uu____15951) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____15966,uu____15967) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____15981,uu____15982) ->
            fail "bottom"
        | (uu____15990,FStar_Syntax_Syntax.Tm_bvar uu____15991) ->
            fail "bottom"
        | (uu____15993,FStar_Syntax_Syntax.Tm_name uu____15994) ->
            fail "bottom"
        | (uu____15996,FStar_Syntax_Syntax.Tm_fvar uu____15997) ->
            fail "bottom"
        | (uu____15999,FStar_Syntax_Syntax.Tm_constant uu____16000) ->
            fail "bottom"
        | (uu____16002,FStar_Syntax_Syntax.Tm_type uu____16003) ->
            fail "bottom"
        | (uu____16005,FStar_Syntax_Syntax.Tm_abs uu____16006) ->
            fail "bottom"
        | (uu____16026,FStar_Syntax_Syntax.Tm_arrow uu____16027) ->
            fail "bottom"
        | (uu____16043,FStar_Syntax_Syntax.Tm_refine uu____16044) ->
            fail "bottom"
        | (uu____16052,FStar_Syntax_Syntax.Tm_app uu____16053) ->
            fail "bottom"
        | (uu____16071,FStar_Syntax_Syntax.Tm_match uu____16072) ->
            fail "bottom"
        | (uu____16096,FStar_Syntax_Syntax.Tm_let uu____16097) ->
            fail "bottom"
        | (uu____16112,FStar_Syntax_Syntax.Tm_uvar uu____16113) ->
            fail "bottom"
        | (uu____16127,FStar_Syntax_Syntax.Tm_meta uu____16128) ->
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
               let uu____16163 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16163)
          (fun q1  ->
             fun q2  ->
               let uu____16175 =
                 let uu____16177 = eq_aqual q1 q2  in uu____16177 = Equal  in
               check "arg qual" uu____16175) a1 a2

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
               let uu____16202 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16202)
          (fun q1  ->
             fun q2  ->
               let uu____16214 =
                 let uu____16216 = eq_aqual q1 q2  in uu____16216 = Equal  in
               check "binder qual" uu____16214) b1 b2

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
        ((let uu____16230 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16230) &&
           (let uu____16234 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16234))
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
    fun uu____16244  ->
      fun uu____16245  ->
        match (uu____16244, uu____16245) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16372 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16372) &&
               (let uu____16376 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16376))
              &&
              (let uu____16380 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16422 -> false  in
               check "branch when" uu____16380)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16443 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16443) &&
           (let uu____16452 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16452))
          &&
          (let uu____16456 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16456)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16473 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16473 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16527 ->
        let uu____16542 =
          let uu____16544 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16544  in
        Prims.int_one + uu____16542
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16547 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16547
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16551 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16551
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16560 = sizeof t1  in (FStar_List.length us) + uu____16560
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16564) ->
        let uu____16589 = sizeof t1  in
        let uu____16591 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16606  ->
                 match uu____16606 with
                 | (bv,uu____16616) ->
                     let uu____16621 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16621) Prims.int_zero bs
           in
        uu____16589 + uu____16591
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____16650 = sizeof hd1  in
        let uu____16652 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16667  ->
                 match uu____16667 with
                 | (arg,uu____16677) ->
                     let uu____16682 = sizeof arg  in acc + uu____16682)
            Prims.int_zero args
           in
        uu____16650 + uu____16652
    | uu____16685 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16699 =
        let uu____16700 = un_uinst t  in uu____16700.FStar_Syntax_Syntax.n
         in
      match uu____16699 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16705 -> false
  
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
           let uu____16766 = head_and_args t  in
           match uu____16766 with
           | (head1,args) ->
               let uu____16821 =
                 let uu____16822 = FStar_Syntax_Subst.compress head1  in
                 uu____16822.FStar_Syntax_Syntax.n  in
               (match uu____16821 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16848 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____16881 = is_fvar attr a  in Prims.op_Negation uu____16881)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options1 s =
        let uu____16902 = FStar_Options.set_options s  in
        match uu____16902 with
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
          ((let uu____16916 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16916 (fun a1  -> ()));
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
          let uu____16931 = FStar_Options.internal_pop ()  in
          if uu____16931
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
    | FStar_Syntax_Syntax.Tm_delayed uu____16963 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____16982 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____16997 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____16998 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____16999 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17008) ->
        let uu____17033 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17033 with
         | (bs1,t2) ->
             let uu____17042 =
               FStar_List.collect
                 (fun uu____17054  ->
                    match uu____17054 with
                    | (b,uu____17064) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17069 = unbound_variables t2  in
             FStar_List.append uu____17042 uu____17069)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17094 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17094 with
         | (bs1,c1) ->
             let uu____17103 =
               FStar_List.collect
                 (fun uu____17115  ->
                    match uu____17115 with
                    | (b,uu____17125) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17130 = unbound_variables_comp c1  in
             FStar_List.append uu____17103 uu____17130)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17139 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17139 with
         | (bs,t2) ->
             let uu____17162 =
               FStar_List.collect
                 (fun uu____17174  ->
                    match uu____17174 with
                    | (b1,uu____17184) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17189 = unbound_variables t2  in
             FStar_List.append uu____17162 uu____17189)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17218 =
          FStar_List.collect
            (fun uu____17232  ->
               match uu____17232 with
               | (x,uu____17244) -> unbound_variables x) args
           in
        let uu____17253 = unbound_variables t1  in
        FStar_List.append uu____17218 uu____17253
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17294 = unbound_variables t1  in
        let uu____17297 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17312 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17312 with
                  | (p,wopt,t2) ->
                      let uu____17334 = unbound_variables t2  in
                      let uu____17337 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17334 uu____17337))
           in
        FStar_List.append uu____17294 uu____17297
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17351) ->
        let uu____17392 = unbound_variables t1  in
        let uu____17395 =
          let uu____17398 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17429 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17398 uu____17429  in
        FStar_List.append uu____17392 uu____17395
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17470 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17473 =
          let uu____17476 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17479 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17484 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17486 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17486 with
                 | (uu____17507,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17476 uu____17479  in
        FStar_List.append uu____17470 uu____17473
    | FStar_Syntax_Syntax.Tm_let ((uu____17509,lbs),t1) ->
        let uu____17529 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17529 with
         | (lbs1,t2) ->
             let uu____17544 = unbound_variables t2  in
             let uu____17547 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17554 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17557 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17554 uu____17557) lbs1
                in
             FStar_List.append uu____17544 uu____17547)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17574 = unbound_variables t1  in
        let uu____17577 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17582,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17637  ->
                      match uu____17637 with
                      | (a,uu____17649) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17658,uu____17659,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17665,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17671 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17680 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17681 -> []  in
        FStar_List.append uu____17574 uu____17577

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17688) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17698) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17708 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17711 =
          FStar_List.collect
            (fun uu____17725  ->
               match uu____17725 with
               | (a,uu____17737) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17708 uu____17711

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
            let uu____17852 = head_and_args h  in
            (match uu____17852 with
             | (head1,args) ->
                 let uu____17913 =
                   let uu____17914 = FStar_Syntax_Subst.compress head1  in
                   uu____17914.FStar_Syntax_Syntax.n  in
                 (match uu____17913 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____17967 -> aux (h :: acc) t))
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
      let uu____17991 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____17991 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2479_18033 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2479_18033.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2479_18033.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2479_18033.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2479_18033.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2479_18033.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18041 =
      let uu____18042 = FStar_Syntax_Subst.compress t  in
      uu____18042.FStar_Syntax_Syntax.n  in
    match uu____18041 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18046,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18074)::uu____18075 ->
                  let pats' = unmeta pats  in
                  let uu____18135 = head_and_args pats'  in
                  (match uu____18135 with
                   | (head1,uu____18154) ->
                       let uu____18179 =
                         let uu____18180 = un_uinst head1  in
                         uu____18180.FStar_Syntax_Syntax.n  in
                       (match uu____18179 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18185 -> false))
              | uu____18187 -> false)
         | uu____18199 -> false)
    | uu____18201 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18217 =
      let uu____18234 = unmeta e  in head_and_args uu____18234  in
    match uu____18217 with
    | (head1,args) ->
        let uu____18265 =
          let uu____18280 =
            let uu____18281 = un_uinst head1  in
            uu____18281.FStar_Syntax_Syntax.n  in
          (uu____18280, args)  in
        (match uu____18265 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18299) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18323::(hd1,uu____18325)::(tl1,uu____18327)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18394 =
               let uu____18397 =
                 let uu____18400 = list_elements tl1  in
                 FStar_Util.must uu____18400  in
               hd1 :: uu____18397  in
             FStar_Pervasives_Native.Some uu____18394
         | uu____18409 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18438 =
      let uu____18439 = FStar_Syntax_Subst.compress t  in
      uu____18439.FStar_Syntax_Syntax.n  in
    match uu____18438 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18446) ->
        let uu____18481 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18481 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18515 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18515
             then
               let uu____18522 =
                 let uu____18533 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18533]  in
               mk_app t uu____18522
             else e1)
    | uu____18560 ->
        let uu____18561 =
          let uu____18572 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18572]  in
        mk_app t uu____18561
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18627 = list_elements e  in
        match uu____18627 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18662 =
          let uu____18679 = unmeta p  in
          FStar_All.pipe_right uu____18679 head_and_args  in
        match uu____18662 with
        | (head1,args) ->
            let uu____18730 =
              let uu____18745 =
                let uu____18746 = un_uinst head1  in
                uu____18746.FStar_Syntax_Syntax.n  in
              (uu____18745, args)  in
            (match uu____18730 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18768,uu____18769)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18821 ->
                 let uu____18836 =
                   let uu____18842 =
                     let uu____18844 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18844
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____18842)  in
                 FStar_Errors.raise_error uu____18836
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____18887 =
            let uu____18904 = unmeta t1  in
            FStar_All.pipe_right uu____18904 head_and_args  in
          match uu____18887 with
          | (head1,args) ->
              let uu____18951 =
                let uu____18966 =
                  let uu____18967 = un_uinst head1  in
                  uu____18967.FStar_Syntax_Syntax.n  in
                (uu____18966, args)  in
              (match uu____18951 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____18986)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19023 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19053 = smt_pat_or t1  in
            (match uu____19053 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19075 = list_elements1 e  in
                 FStar_All.pipe_right uu____19075
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19105 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19105
                           (FStar_List.map one_pat)))
             | uu____19134 ->
                 let uu____19139 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19139])
        | uu____19194 ->
            let uu____19197 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19197]
         in
      let uu____19252 =
        let uu____19285 =
          let uu____19286 = FStar_Syntax_Subst.compress t  in
          uu____19286.FStar_Syntax_Syntax.n  in
        match uu____19285 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19343 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19343 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19414;
                        FStar_Syntax_Syntax.effect_name = uu____19415;
                        FStar_Syntax_Syntax.result_typ = uu____19416;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19418)::(post,uu____19420)::(pats,uu____19422)::[];
                        FStar_Syntax_Syntax.flags = uu____19423;_}
                      ->
                      let uu____19484 = lemma_pats pats  in
                      (binders1, pre, post, uu____19484)
                  | uu____19521 -> failwith "impos"))
        | uu____19555 -> failwith "Impos"  in
      match uu____19252 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19647 =
              let uu____19654 =
                let uu____19655 =
                  let uu____19662 = mk_imp pre post1  in
                  let uu____19665 =
                    let uu____19666 =
                      let uu____19687 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19687, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19666  in
                  (uu____19662, uu____19665)  in
                FStar_Syntax_Syntax.Tm_meta uu____19655  in
              FStar_Syntax_Syntax.mk uu____19654  in
            uu____19647 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19711 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19711 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19741 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19752 -> true
    | uu____19754 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19765 -> true
    | uu____19767 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19785 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19786 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19787 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19788 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19789 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19790 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19791 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19792 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19795 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19798 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19785;
        FStar_Syntax_Syntax.bind_wp = uu____19786;
        FStar_Syntax_Syntax.stronger = uu____19787;
        FStar_Syntax_Syntax.if_then_else = uu____19788;
        FStar_Syntax_Syntax.ite_wp = uu____19789;
        FStar_Syntax_Syntax.close_wp = uu____19790;
        FStar_Syntax_Syntax.trivial = uu____19791;
        FStar_Syntax_Syntax.repr = uu____19792;
        FStar_Syntax_Syntax.return_repr = uu____19795;
        FStar_Syntax_Syntax.bind_repr = uu____19798
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____19830 =
        match uu____19830 with
        | (ts1,ts2) ->
            let uu____19841 = f ts1  in
            let uu____19842 = f ts2  in (uu____19841, uu____19842)
         in
      let uu____19843 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____19848 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____19853 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____19858 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____19863 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____19843;
        FStar_Syntax_Syntax.l_return = uu____19848;
        FStar_Syntax_Syntax.l_bind = uu____19853;
        FStar_Syntax_Syntax.l_subcomp = uu____19858;
        FStar_Syntax_Syntax.l_if_then_else = uu____19863
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
          let uu____19885 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____19885
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19887 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____19887
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19889 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____19889
  
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
    | uu____19904 -> FStar_Pervasives_Native.None
  
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
        let uu____19918 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19918
          (fun _19925  -> FStar_Pervasives_Native.Some _19925)
  
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
        let uu____19965 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19965
          (fun _19972  -> FStar_Pervasives_Native.Some _19972)
  
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
        let uu____19986 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19986
          (fun _19993  -> FStar_Pervasives_Native.Some _19993)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun _20007  -> FStar_Pervasives_Native.Some _20007)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun _20011  -> FStar_Pervasives_Native.Some _20011)
    | uu____20012 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20024 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20024
          (fun _20031  -> FStar_Pervasives_Native.Some _20031)
    | uu____20032 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun _20046  -> FStar_Pervasives_Native.Some _20046)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun _20050  -> FStar_Pervasives_Native.Some _20050)
    | uu____20051 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun _20065  -> FStar_Pervasives_Native.Some _20065)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun _20069  -> FStar_Pervasives_Native.Some _20069)
    | uu____20070 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20094 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20095 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20097 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20097
          (fun _20104  -> FStar_Pervasives_Native.Some _20104)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun _20118  -> FStar_Pervasives_Native.Some _20118)
    | uu____20119 -> FStar_Pervasives_Native.None
  