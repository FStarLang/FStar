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
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
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
<<<<<<< HEAD
<<<<<<< HEAD
      | uu____2835 -> false
  
let rec unlazy_as_t :
  'Auu____2848 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2848
  =
  fun k  ->
    fun t  ->
      let uu____2859 =
        let uu____2860 = FStar_Syntax_Subst.compress t  in
        uu____2860.FStar_Syntax_Syntax.n  in
      match uu____2859 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2865;
            FStar_Syntax_Syntax.rng = uu____2866;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____2869 -> failwith "Not a Tm_lazy of the expected kind"
=======
=======
>>>>>>> snap
      | uu____2893 -> false
  
let rec unlazy_as_t :
  'Auu____2906 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____2906
  =
  fun k  ->
    fun t  ->
      let uu____2917 =
        let uu____2918 = FStar_Syntax_Subst.compress t  in
        uu____2918.FStar_Syntax_Syntax.n  in
      match uu____2917 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2923;
            FStar_Syntax_Syntax.rng = uu____2924;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____2927 -> failwith "Not a Tm_lazy of the expected kind"
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
            let uu____2910 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2910;
=======
            let uu____2968 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2968;
>>>>>>> snap
=======
            let uu____2968 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2968;
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____2923 =
      let uu____2938 = unascribe t  in head_and_args' uu____2938  in
    match uu____2923 with
=======
    let uu____2981 =
      let uu____2996 = unascribe t  in head_and_args' uu____2996  in
    match uu____2981 with
>>>>>>> snap
=======
    let uu____2981 =
      let uu____2996 = unascribe t  in head_and_args' uu____2996  in
    match uu____2981 with
>>>>>>> snap
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Equal  -> true | uu____2972 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2983 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2994 -> false
=======
=======
>>>>>>> snap
    match projectee with | Equal  -> true | uu____3030 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____3041 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____3052 -> false
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
      | (NotEqual ,uu____3044) -> NotEqual
      | (uu____3045,NotEqual ) -> NotEqual
      | (Unknown ,uu____3046) -> Unknown
      | (uu____3047,Unknown ) -> Unknown
=======
=======
>>>>>>> snap
      | (NotEqual ,uu____3102) -> NotEqual
      | (uu____3103,NotEqual ) -> NotEqual
      | (Unknown ,uu____3104) -> Unknown
      | (uu____3105,Unknown ) -> Unknown
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
<<<<<<< HEAD
<<<<<<< HEAD
      let equal_if uu___5_3168 = if uu___5_3168 then Equal else Unknown  in
      let equal_iff uu___6_3179 = if uu___6_3179 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____3200 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3222 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3222
        then
          let uu____3226 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3303  ->
                    match uu____3303 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3344 = eq_tm a1 a2  in
                        eq_inj acc uu____3344) Equal) uu____3226
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3358 =
          let uu____3375 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3375 head_and_args  in
        match uu____3358 with
        | (head1,args1) ->
            let uu____3428 =
              let uu____3445 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3445 head_and_args  in
            (match uu____3428 with
             | (head2,args2) ->
                 let uu____3498 =
                   let uu____3503 =
                     let uu____3504 = un_uinst head1  in
                     uu____3504.FStar_Syntax_Syntax.n  in
                   let uu____3507 =
                     let uu____3508 = un_uinst head2  in
                     uu____3508.FStar_Syntax_Syntax.n  in
                   (uu____3503, uu____3507)  in
                 (match uu____3498 with
=======
=======
>>>>>>> snap
      let equal_if uu___9_3226 = if uu___9_3226 then Equal else Unknown  in
      let equal_iff uu___10_3237 = if uu___10_3237 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____3258 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3280 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3280
        then
          let uu____3284 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3361  ->
                    match uu____3361 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3402 = eq_tm a1 a2  in
                        eq_inj acc uu____3402) Equal) uu____3284
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3416 =
          let uu____3433 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3433 head_and_args  in
        match uu____3416 with
        | (head1,args1) ->
            let uu____3486 =
              let uu____3503 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3503 head_and_args  in
            (match uu____3486 with
             | (head2,args2) ->
                 let uu____3556 =
                   let uu____3561 =
                     let uu____3562 = un_uinst head1  in
                     uu____3562.FStar_Syntax_Syntax.n  in
                   let uu____3565 =
                     let uu____3566 = un_uinst head2  in
                     uu____3566.FStar_Syntax_Syntax.n  in
                   (uu____3561, uu____3565)  in
                 (match uu____3556 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                  | uu____3535 -> FStar_Pervasives_Native.None))
         in
      let uu____3548 =
        let uu____3553 =
          let uu____3554 = unmeta t11  in uu____3554.FStar_Syntax_Syntax.n
           in
        let uu____3557 =
          let uu____3558 = unmeta t21  in uu____3558.FStar_Syntax_Syntax.n
           in
        (uu____3553, uu____3557)  in
      match uu____3548 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3564,uu____3565) ->
          let uu____3566 = unlazy t11  in eq_tm uu____3566 t21
      | (uu____3567,FStar_Syntax_Syntax.Tm_lazy uu____3568) ->
          let uu____3569 = unlazy t21  in eq_tm t11 uu____3569
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____3572 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3596 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3596
            (fun uu____3644  ->
               match uu____3644 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3659 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3659
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3673 = eq_tm f g  in
          eq_and uu____3673
            (fun uu____3676  ->
               let uu____3677 = eq_univs_list us vs  in equal_if uu____3677)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3679),uu____3680) -> Unknown
      | (uu____3681,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3682)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3685 = FStar_Const.eq_const c d  in equal_iff uu____3685
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3688)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3690))) ->
          let uu____3719 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3719
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3773 =
            let uu____3778 =
              let uu____3779 = un_uinst h1  in
              uu____3779.FStar_Syntax_Syntax.n  in
            let uu____3782 =
              let uu____3783 = un_uinst h2  in
              uu____3783.FStar_Syntax_Syntax.n  in
            (uu____3778, uu____3782)  in
          (match uu____3773 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3789 =
                    let uu____3791 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3791  in
                  FStar_List.mem uu____3789 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3793 ->
               let uu____3798 = eq_tm h1 h2  in
               eq_and uu____3798 (fun uu____3800  -> eq_args args1 args2))
=======
=======
>>>>>>> snap
                  | uu____3593 -> FStar_Pervasives_Native.None))
         in
      let uu____3606 =
        let uu____3611 =
          let uu____3612 = unmeta t11  in uu____3612.FStar_Syntax_Syntax.n
           in
        let uu____3615 =
          let uu____3616 = unmeta t21  in uu____3616.FStar_Syntax_Syntax.n
           in
        (uu____3611, uu____3615)  in
      match uu____3606 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3622,uu____3623) ->
          let uu____3624 = unlazy t11  in eq_tm uu____3624 t21
      | (uu____3625,FStar_Syntax_Syntax.Tm_lazy uu____3626) ->
          let uu____3627 = unlazy t21  in eq_tm t11 uu____3627
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____3630 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3654 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3654
            (fun uu____3702  ->
               match uu____3702 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3717 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3717
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3731 = eq_tm f g  in
          eq_and uu____3731
            (fun uu____3734  ->
               let uu____3735 = eq_univs_list us vs  in equal_if uu____3735)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3737),uu____3738) -> Unknown
      | (uu____3739,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3740)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3743 = FStar_Const.eq_const c d  in equal_iff uu____3743
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3746)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3748))) ->
          let uu____3777 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3777
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3831 =
            let uu____3836 =
              let uu____3837 = un_uinst h1  in
              uu____3837.FStar_Syntax_Syntax.n  in
            let uu____3840 =
              let uu____3841 = un_uinst h2  in
              uu____3841.FStar_Syntax_Syntax.n  in
            (uu____3836, uu____3840)  in
          (match uu____3831 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3847 =
                    let uu____3849 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3849  in
                  FStar_List.mem uu____3847 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3851 ->
               let uu____3856 = eq_tm h1 h2  in
               eq_and uu____3856 (fun uu____3858  -> eq_args args1 args2))
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
<<<<<<< HEAD
<<<<<<< HEAD
            let uu____3906 = FStar_List.zip bs1 bs2  in
            let uu____3969 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____4006  ->
                 fun a  ->
                   match uu____4006 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4099  -> branch_matches b1 b2))
              uu____3906 uu____3969
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____4104 = eq_univs u v1  in equal_if uu____4104
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____4118 = eq_quoteinfo q1 q2  in
          eq_and uu____4118 (fun uu____4120  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____4133 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4133 (fun uu____4135  -> eq_tm phi1 phi2)
      | uu____4136 -> Unknown
=======
=======
>>>>>>> snap
            let uu____3964 = FStar_List.zip bs1 bs2  in
            let uu____4027 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____4064  ->
                 fun a  ->
                   match uu____4064 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4157  -> branch_matches b1 b2))
              uu____3964 uu____4027
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____4162 = eq_univs u v1  in equal_if uu____4162
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____4176 = eq_quoteinfo q1 q2  in
          eq_and uu____4176 (fun uu____4178  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____4191 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4191 (fun uu____4193  -> eq_tm phi1 phi2)
      | uu____4194 -> Unknown
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap

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
<<<<<<< HEAD
<<<<<<< HEAD
      | ([],uu____4208) -> NotEqual
      | (uu____4239,[]) -> NotEqual
=======
      | ([],uu____4266) -> NotEqual
      | (uu____4297,[]) -> NotEqual
>>>>>>> snap
=======
      | ([],uu____4266) -> NotEqual
      | (uu____4297,[]) -> NotEqual
>>>>>>> snap
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
<<<<<<< HEAD
<<<<<<< HEAD
            (let uu____4331 = eq_tm t1 t2  in
             match uu____4331 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4332 = eq_antiquotes a11 a21  in
                 (match uu____4332 with
                  | NotEqual  -> NotEqual
                  | uu____4333 -> Unknown)
=======
            (let uu____4389 = eq_tm t1 t2  in
             match uu____4389 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4390 = eq_antiquotes a11 a21  in
                 (match uu____4390 with
                  | NotEqual  -> NotEqual
                  | uu____4391 -> Unknown)
>>>>>>> snap
=======
            (let uu____4389 = eq_tm t1 t2  in
             match uu____4389 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4390 = eq_antiquotes a11 a21  in
                 (match uu____4390 with
                  | NotEqual  -> NotEqual
                  | uu____4391 -> Unknown)
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
      | (FStar_Pervasives_Native.None ,uu____4348) -> NotEqual
      | (uu____4355,FStar_Pervasives_Native.None ) -> NotEqual
=======
      | (FStar_Pervasives_Native.None ,uu____4406) -> NotEqual
      | (uu____4413,FStar_Pervasives_Native.None ) -> NotEqual
>>>>>>> snap
=======
      | (FStar_Pervasives_Native.None ,uu____4406) -> NotEqual
      | (uu____4413,FStar_Pervasives_Native.None ) -> NotEqual
>>>>>>> snap
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
<<<<<<< HEAD
<<<<<<< HEAD
      | uu____4385 -> NotEqual
=======
      | uu____4443 -> NotEqual
>>>>>>> snap
=======
      | uu____4443 -> NotEqual
>>>>>>> snap

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
<<<<<<< HEAD
<<<<<<< HEAD
        | (uu____4477,uu____4478) -> false  in
      let uu____4488 = b1  in
      match uu____4488 with
      | (p1,w1,t1) ->
          let uu____4522 = b2  in
          (match uu____4522 with
           | (p2,w2,t2) ->
               let uu____4556 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4556
               then
                 let uu____4559 =
                   (let uu____4563 = eq_tm t1 t2  in uu____4563 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4572 = eq_tm t11 t21  in
                             uu____4572 = Equal) w1 w2)
                    in
                 (if uu____4559 then Equal else Unknown)
=======
=======
>>>>>>> snap
        | (uu____4535,uu____4536) -> false  in
      let uu____4546 = b1  in
      match uu____4546 with
      | (p1,w1,t1) ->
          let uu____4580 = b2  in
          (match uu____4580 with
           | (p2,w2,t2) ->
               let uu____4614 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4614
               then
                 let uu____4617 =
                   (let uu____4621 = eq_tm t1 t2  in uu____4621 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4630 = eq_tm t11 t21  in
                             uu____4630 = Equal) w1 w2)
                    in
                 (if uu____4617 then Equal else Unknown)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
<<<<<<< HEAD
<<<<<<< HEAD
      | ((a,uu____4637)::a11,(b,uu____4640)::b1) ->
          let uu____4714 = eq_tm a b  in
          (match uu____4714 with
           | Equal  -> eq_args a11 b1
           | uu____4715 -> Unknown)
      | uu____4716 -> Unknown
=======
      | ((a,uu____4695)::a11,(b,uu____4698)::b1) ->
          let uu____4772 = eq_tm a b  in
          (match uu____4772 with
           | Equal  -> eq_args a11 b1
           | uu____4773 -> Unknown)
      | uu____4774 -> Unknown
>>>>>>> snap
=======
      | ((a,uu____4695)::a11,(b,uu____4698)::b1) ->
          let uu____4772 = eq_tm a b  in
          (match uu____4772 with
           | Equal  -> eq_args a11 b1
           | uu____4773 -> Unknown)
      | uu____4774 -> Unknown
>>>>>>> snap

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
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4752) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4758,uu____4759) ->
        unrefine t2
    | uu____4800 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4808 =
      let uu____4809 = FStar_Syntax_Subst.compress t  in
      uu____4809.FStar_Syntax_Syntax.n  in
    match uu____4808 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4813 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4828) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4833 ->
        let uu____4850 =
          let uu____4851 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4851 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4850 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4914,uu____4915) ->
        is_uvar t1
    | uu____4956 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4965 =
      let uu____4966 = unrefine t  in uu____4966.FStar_Syntax_Syntax.n  in
    match uu____4965 with
=======
=======
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4810) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4816,uu____4817) ->
        unrefine t2
    | uu____4858 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4866 =
      let uu____4867 = FStar_Syntax_Subst.compress t  in
      uu____4867.FStar_Syntax_Syntax.n  in
    match uu____4866 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4871 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4886) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4891 ->
        let uu____4908 =
          let uu____4909 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4909 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4908 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4972,uu____4973) ->
        is_uvar t1
    | uu____5014 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5023 =
      let uu____5024 = unrefine t  in uu____5024.FStar_Syntax_Syntax.n  in
    match uu____5023 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_app (head1,uu____4972) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4998) -> is_unit t1
    | uu____5003 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5012 =
      let uu____5013 = FStar_Syntax_Subst.compress t  in
      uu____5013.FStar_Syntax_Syntax.n  in
    match uu____5012 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5018 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5027 =
      let uu____5028 = unrefine t  in uu____5028.FStar_Syntax_Syntax.n  in
    match uu____5027 with
    | FStar_Syntax_Syntax.Tm_type uu____5032 -> true
=======
=======
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_app (head1,uu____5030) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5056) -> is_unit t1
    | uu____5061 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5070 =
      let uu____5071 = FStar_Syntax_Subst.compress t  in
      uu____5071.FStar_Syntax_Syntax.n  in
    match uu____5070 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5076 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5085 =
      let uu____5086 = unrefine t  in uu____5086.FStar_Syntax_Syntax.n  in
    match uu____5085 with
    | FStar_Syntax_Syntax.Tm_type uu____5090 -> true
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_app (head1,uu____5036) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5062) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____5067,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____5089 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5098 =
      let uu____5099 = FStar_Syntax_Subst.compress e  in
      uu____5099.FStar_Syntax_Syntax.n  in
    match uu____5098 with
    | FStar_Syntax_Syntax.Tm_abs uu____5103 -> true
    | uu____5123 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5132 =
      let uu____5133 = FStar_Syntax_Subst.compress t  in
      uu____5133.FStar_Syntax_Syntax.n  in
    match uu____5132 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5137 -> true
    | uu____5153 -> false
=======
=======
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_app (head1,uu____5094) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5120) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____5125,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____5147 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5156 =
      let uu____5157 = FStar_Syntax_Subst.compress e  in
      uu____5157.FStar_Syntax_Syntax.n  in
    match uu____5156 with
    | FStar_Syntax_Syntax.Tm_abs uu____5161 -> true
    | uu____5181 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5190 =
      let uu____5191 = FStar_Syntax_Subst.compress t  in
      uu____5191.FStar_Syntax_Syntax.n  in
    match uu____5190 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5195 -> true
    | uu____5211 -> false
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5163) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5169,uu____5170) ->
        pre_typ t2
    | uu____5211 -> t1
=======
=======
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5221) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5227,uu____5228) ->
        pre_typ t2
    | uu____5269 -> t1
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____5236 =
        let uu____5237 = un_uinst typ1  in uu____5237.FStar_Syntax_Syntax.n
         in
      match uu____5236 with
=======
=======
>>>>>>> snap
      let uu____5294 =
        let uu____5295 = un_uinst typ1  in uu____5295.FStar_Syntax_Syntax.n
         in
      match uu____5294 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
<<<<<<< HEAD
<<<<<<< HEAD
           | uu____5302 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5332 -> FStar_Pervasives_Native.None
=======
=======
>>>>>>> snap
           | uu____5360 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5390 -> FStar_Pervasives_Native.None
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Sig_let (uu____5353,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5360) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5365,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5376,uu____5377,uu____5378,uu____5379,uu____5380) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5390,uu____5391,uu____5392,uu____5393) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5399,uu____5400,uu____5401,uu____5402,uu____5403) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5411,uu____5412) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5414,uu____5415) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5418 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5419 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5420 -> []
=======
=======
>>>>>>> snap
    | FStar_Syntax_Syntax.Sig_let (uu____5411,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5418) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5423,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5434,uu____5435,uu____5436,uu____5437,uu____5438) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5448,uu____5449,uu____5450,uu____5451) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5457,uu____5458,uu____5459,uu____5460,uu____5461) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5469,uu____5470) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5472,uu____5473) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5476 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5477 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5478 -> []
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____5434 -> FStar_Pervasives_Native.None
=======
    | uu____5492 -> FStar_Pervasives_Native.None
>>>>>>> snap
=======
    | uu____5492 -> FStar_Pervasives_Native.None
>>>>>>> snap
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
<<<<<<< HEAD
<<<<<<< HEAD
  fun uu___7_5460  ->
    match uu___7_5460 with
=======
  fun uu___11_5518  ->
    match uu___11_5518 with
>>>>>>> snap
=======
  fun uu___11_5518  ->
    match uu___11_5518 with
>>>>>>> snap
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
<<<<<<< HEAD
<<<<<<< HEAD
  'Auu____5474 'Auu____5475 .
    ('Auu____5474 FStar_Syntax_Syntax.syntax * 'Auu____5475) ->
      FStar_Range.range
  =
  fun uu____5486  ->
    match uu____5486 with | (hd1,uu____5494) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5508 'Auu____5509 .
    ('Auu____5508 FStar_Syntax_Syntax.syntax * 'Auu____5509) Prims.list ->
=======
=======
>>>>>>> snap
  'Auu____5532 'Auu____5533 .
    ('Auu____5532 FStar_Syntax_Syntax.syntax * 'Auu____5533) ->
      FStar_Range.range
  =
  fun uu____5544  ->
    match uu____5544 with | (hd1,uu____5552) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____5566 'Auu____5567 .
    ('Auu____5566 FStar_Syntax_Syntax.syntax * 'Auu____5567) Prims.list ->
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
      | uu____5607 ->
=======
      | uu____5665 ->
>>>>>>> snap
=======
      | uu____5665 ->
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____5666 =
        FStar_List.map
          (fun uu____5693  ->
             match uu____5693 with
             | (bv,aq) ->
                 let uu____5712 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5712, aq)) bs
         in
      mk_app f uu____5666
=======
=======
>>>>>>> snap
      let uu____5724 =
        FStar_List.map
          (fun uu____5751  ->
             match uu____5751 with
             | (bv,aq) ->
                 let uu____5770 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5770, aq)) bs
         in
      mk_app f uu____5724
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____5762 = FStar_Ident.range_of_lid l  in
          let uu____5763 =
            let uu____5772 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5772  in
          uu____5763 FStar_Pervasives_Native.None uu____5762
      | uu____5777 ->
          let e =
            let uu____5791 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5791 args  in
=======
=======
>>>>>>> snap
          let uu____5820 = FStar_Ident.range_of_lid l  in
          let uu____5821 =
            let uu____5830 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____5830  in
          uu____5821 FStar_Pervasives_Native.None uu____5820
      | uu____5835 ->
          let e =
            let uu____5849 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____5849 args  in
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____5868 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5868
          then
            let uu____5871 =
              let uu____5877 =
                let uu____5879 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5879  in
              let uu____5882 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5877, uu____5882)  in
            FStar_Ident.mk_ident uu____5871
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___957_5887 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___957_5887.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___957_5887.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5888 = mk_field_projector_name_from_ident lid nm  in
        (uu____5888, y)
=======
=======
>>>>>>> snap
          let uu____5926 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5926
          then
            let uu____5929 =
              let uu____5935 =
                let uu____5937 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5937  in
              let uu____5940 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5935, uu____5940)  in
            FStar_Ident.mk_ident uu____5929
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___996_5945 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___996_5945.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___996_5945.FStar_Syntax_Syntax.sort)
          }  in
        let uu____5946 = mk_field_projector_name_from_ident lid nm  in
        (uu____5946, y)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5900) -> ses
    | uu____5909 -> failwith "ses_of_sigbundle: not a Sig_bundle"
=======
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5958) -> ses
    | uu____5967 -> failwith "ses_of_sigbundle: not a Sig_bundle"
>>>>>>> snap
=======
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5958) -> ses
    | uu____5967 -> failwith "ses_of_sigbundle: not a Sig_bundle"
>>>>>>> snap
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____5920 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
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
          let uu____5955 =
            let uu___974_5956 = r  in
            let uu____5957 = f r.FStar_Syntax_Syntax.if_then_else  in
            let uu____5958 = f r.FStar_Syntax_Syntax.ite_wp  in
            let uu____5959 = f r.FStar_Syntax_Syntax.close_wp  in
            {
              FStar_Syntax_Syntax.if_then_else = uu____5957;
              FStar_Syntax_Syntax.ite_wp = uu____5958;
              FStar_Syntax_Syntax.close_wp = uu____5959
            }  in
          FStar_Util.Inl uu____5955
      | FStar_Util.Inr r ->
          let uu____5961 =
            let uu___978_5962 = r  in
            let uu____5963 = f r.FStar_Syntax_Syntax.conjunction  in
            { FStar_Syntax_Syntax.conjunction = uu____5963 }  in
          FStar_Util.Inr uu____5961
  
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
    | uu____5991 ->
        failwith
          "Impossible! get_match_with_close_wps called with a match_with_subst wp"
=======
    | uu____5978 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
>>>>>>> snap
=======
    | uu____5978 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
>>>>>>> snap
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____6014 = FStar_Syntax_Unionfind.find uv  in
      match uu____6014 with
      | FStar_Pervasives_Native.Some uu____6017 ->
          let uu____6018 =
            let uu____6020 =
              let uu____6022 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____6022  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____6020  in
          failwith uu____6018
      | uu____6027 -> FStar_Syntax_Unionfind.change uv t
=======
=======
>>>>>>> snap
      let uu____5991 = FStar_Syntax_Unionfind.find uv  in
      match uu____5991 with
      | FStar_Pervasives_Native.Some uu____5994 ->
          let uu____5995 =
            let uu____5997 =
              let uu____5999 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5999  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5997  in
          failwith uu____5995
      | uu____6004 -> FStar_Syntax_Unionfind.change uv t
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
      | uu____6110 -> q1 = q2
=======
      | uu____6087 -> q1 = q2
>>>>>>> snap
=======
      | uu____6087 -> q1 = q2
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
              let uu____6156 =
                let uu___1032_6157 = rc  in
                let uu____6158 =
=======
              let uu____6133 =
                let uu___1057_6134 = rc  in
                let uu____6135 =
>>>>>>> snap
=======
              let uu____6133 =
                let uu___1057_6134 = rc  in
                let uu____6135 =
>>>>>>> snap
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
<<<<<<< HEAD
<<<<<<< HEAD
                    (uu___1032_6157.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6158;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1032_6157.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6156
           in
        match bs with
        | [] -> t
        | uu____6175 ->
            let body =
              let uu____6177 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6177  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6207 =
                   let uu____6214 =
                     let uu____6215 =
                       let uu____6234 =
                         let uu____6243 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6243 bs'  in
                       let uu____6258 = close_lopt lopt'  in
                       (uu____6234, t1, uu____6258)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6215  in
                   FStar_Syntax_Syntax.mk uu____6214  in
                 uu____6207 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6273 ->
                 let uu____6274 =
                   let uu____6281 =
                     let uu____6282 =
                       let uu____6301 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6310 = close_lopt lopt  in
                       (uu____6301, body, uu____6310)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6282  in
                   FStar_Syntax_Syntax.mk uu____6281  in
                 uu____6274 FStar_Pervasives_Native.None
=======
=======
>>>>>>> snap
                    (uu___1057_6134.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6135;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1057_6134.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6133
           in
        match bs with
        | [] -> t
        | uu____6152 ->
            let body =
              let uu____6154 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6154  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6184 =
                   let uu____6191 =
                     let uu____6192 =
                       let uu____6211 =
                         let uu____6220 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6220 bs'  in
                       let uu____6235 = close_lopt lopt'  in
                       (uu____6211, t1, uu____6235)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6192  in
                   FStar_Syntax_Syntax.mk uu____6191  in
                 uu____6184 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6250 ->
                 let uu____6251 =
                   let uu____6258 =
                     let uu____6259 =
                       let uu____6278 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6287 = close_lopt lopt  in
                       (uu____6278, body, uu____6287)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6259  in
                   FStar_Syntax_Syntax.mk uu____6258  in
                 uu____6251 FStar_Pervasives_Native.None
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
      | uu____6366 ->
          let uu____6375 =
            let uu____6382 =
              let uu____6383 =
                let uu____6398 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6407 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6398, uu____6407)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6383  in
            FStar_Syntax_Syntax.mk uu____6382  in
          uu____6375 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
=======
=======
>>>>>>> snap
      | uu____6343 ->
          let uu____6352 =
            let uu____6359 =
              let uu____6360 =
                let uu____6375 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6384 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6375, uu____6384)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6360  in
            FStar_Syntax_Syntax.mk uu____6359  in
          uu____6352 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____6456 =
        let uu____6457 = FStar_Syntax_Subst.compress t  in
        uu____6457.FStar_Syntax_Syntax.n  in
      match uu____6456 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6487) ->
               let uu____6496 =
                 let uu____6497 = FStar_Syntax_Subst.compress tres  in
                 uu____6497.FStar_Syntax_Syntax.n  in
               (match uu____6496 with
=======
      let uu____6433 =
        let uu____6434 = FStar_Syntax_Subst.compress t  in
        uu____6434.FStar_Syntax_Syntax.n  in
      match uu____6433 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
=======
      let uu____6433 =
        let uu____6434 = FStar_Syntax_Subst.compress t  in
        uu____6434.FStar_Syntax_Syntax.n  in
      match uu____6433 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
>>>>>>> snap
           | FStar_Syntax_Syntax.Total (tres,uu____6464) ->
               let uu____6473 =
                 let uu____6474 = FStar_Syntax_Subst.compress tres  in
                 uu____6474.FStar_Syntax_Syntax.n  in
               (match uu____6473 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
<<<<<<< HEAD
                | uu____6540 -> t)
           | uu____6541 -> t)
      | uu____6542 -> t
=======
                | uu____6517 -> t)
           | uu____6518 -> t)
      | uu____6519 -> t
>>>>>>> snap
=======
                | uu____6517 -> t)
           | uu____6518 -> t)
      | uu____6519 -> t
>>>>>>> snap
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____6560 =
        let uu____6561 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6561 t.FStar_Syntax_Syntax.pos  in
      let uu____6562 =
        let uu____6569 =
          let uu____6570 =
            let uu____6577 =
              let uu____6580 =
                let uu____6581 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6581]  in
              FStar_Syntax_Subst.close uu____6580 t  in
            (b, uu____6577)  in
          FStar_Syntax_Syntax.Tm_refine uu____6570  in
        FStar_Syntax_Syntax.mk uu____6569  in
      uu____6562 FStar_Pervasives_Native.None uu____6560
=======
=======
>>>>>>> snap
      let uu____6537 =
        let uu____6538 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6538 t.FStar_Syntax_Syntax.pos  in
      let uu____6539 =
        let uu____6546 =
          let uu____6547 =
            let uu____6554 =
              let uu____6557 =
                let uu____6558 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6558]  in
              FStar_Syntax_Subst.close uu____6557 t  in
            (b, uu____6554)  in
          FStar_Syntax_Syntax.Tm_refine uu____6547  in
        FStar_Syntax_Syntax.mk uu____6546  in
      uu____6539 FStar_Pervasives_Native.None uu____6537
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____6661 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6661 with
         | (bs1,c1) ->
             let uu____6680 = is_total_comp c1  in
             if uu____6680
             then
               let uu____6695 = arrow_formals_comp (comp_result c1)  in
               (match uu____6695 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6762;
           FStar_Syntax_Syntax.index = uu____6763;
           FStar_Syntax_Syntax.sort = s;_},uu____6765)
        ->
        let rec aux s1 k2 =
          let uu____6796 =
            let uu____6797 = FStar_Syntax_Subst.compress s1  in
            uu____6797.FStar_Syntax_Syntax.n  in
          match uu____6796 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6812 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6827;
                 FStar_Syntax_Syntax.index = uu____6828;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6830)
              -> aux s2 k2
          | uu____6838 ->
              let uu____6839 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6839)
           in
        aux s k1
    | uu____6854 ->
        let uu____6855 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6855)
=======
=======
>>>>>>> snap
        let uu____6638 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____6638 with
         | (bs1,c1) ->
             let uu____6657 = is_total_comp c1  in
             if uu____6657
             then
               let uu____6672 = arrow_formals_comp (comp_result c1)  in
               (match uu____6672 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6739;
           FStar_Syntax_Syntax.index = uu____6740;
           FStar_Syntax_Syntax.sort = s;_},uu____6742)
        ->
        let rec aux s1 k2 =
          let uu____6773 =
            let uu____6774 = FStar_Syntax_Subst.compress s1  in
            uu____6774.FStar_Syntax_Syntax.n  in
          match uu____6773 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6789 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6804;
                 FStar_Syntax_Syntax.index = uu____6805;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6807)
              -> aux s2 k2
          | uu____6815 ->
              let uu____6816 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6816)
           in
        aux s k1
    | uu____6831 ->
        let uu____6832 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6832)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____6890 = arrow_formals_comp k  in
    match uu____6890 with | (bs,c) -> (bs, (comp_result c))
=======
    let uu____6867 = arrow_formals_comp k  in
    match uu____6867 with | (bs,c) -> (bs, (comp_result c))
>>>>>>> snap
=======
    let uu____6867 = arrow_formals_comp k  in
    match uu____6867 with | (bs,c) -> (bs, (comp_result c))
>>>>>>> snap
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____7032 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7032 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____7056 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_7065  ->
                         match uu___8_7065 with
                         | FStar_Syntax_Syntax.DECREASES uu____7067 -> true
                         | uu____7071 -> false))
                  in
               (match uu____7056 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7106 ->
                    let uu____7109 = is_total_comp c1  in
                    if uu____7109
                    then
                      let uu____7128 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7128 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7221;
             FStar_Syntax_Syntax.index = uu____7222;
             FStar_Syntax_Syntax.sort = k2;_},uu____7224)
          -> arrow_until_decreases k2
      | uu____7232 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7253 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7253 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7307 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7328 =
                 FStar_Common.tabulate n_univs (fun uu____7334  -> false)  in
               let uu____7337 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7362  ->
                         match uu____7362 with
                         | (x,uu____7371) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7328 uu____7337)
           in
        ((n_univs + (FStar_List.length bs)), uu____7307)
=======
=======
>>>>>>> snap
          let uu____7009 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7009 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____7033 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___12_7042  ->
                         match uu___12_7042 with
                         | FStar_Syntax_Syntax.DECREASES uu____7044 -> true
                         | uu____7048 -> false))
                  in
               (match uu____7033 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7083 ->
                    let uu____7086 = is_total_comp c1  in
                    if uu____7086
                    then
                      let uu____7105 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7105 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7198;
             FStar_Syntax_Syntax.index = uu____7199;
             FStar_Syntax_Syntax.sort = k2;_},uu____7201)
          -> arrow_until_decreases k2
      | uu____7209 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7230 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7230 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7284 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7305 =
                 FStar_Common.tabulate n_univs (fun uu____7311  -> false)  in
               let uu____7314 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7339  ->
                         match uu____7339 with
                         | (x,uu____7348) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7305 uu____7314)
           in
        ((n_univs + (FStar_List.length bs)), uu____7284)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____7427 =
            let uu___1154_7428 = rc  in
            let uu____7429 =
=======
          let uu____7404 =
            let uu___1179_7405 = rc  in
            let uu____7406 =
>>>>>>> snap
=======
          let uu____7404 =
            let uu___1179_7405 = rc  in
            let uu____7406 =
>>>>>>> snap
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
<<<<<<< HEAD
<<<<<<< HEAD
                (uu___1154_7428.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7429;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1154_7428.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7427
      | uu____7438 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7472 =
        let uu____7473 =
          let uu____7476 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7476  in
        uu____7473.FStar_Syntax_Syntax.n  in
      match uu____7472 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7522 = aux t2 what  in
          (match uu____7522 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7594 -> ([], t1, abs_body_lcomp)  in
    let uu____7611 = aux t FStar_Pervasives_Native.None  in
    match uu____7611 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7659 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7659 with
=======
=======
>>>>>>> snap
                (uu___1179_7405.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7406;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1179_7405.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7404
      | uu____7415 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7449 =
        let uu____7450 =
          let uu____7453 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7453  in
        uu____7450.FStar_Syntax_Syntax.n  in
      match uu____7449 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7499 = aux t2 what  in
          (match uu____7499 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7571 -> ([], t1, abs_body_lcomp)  in
    let uu____7588 = aux t FStar_Pervasives_Native.None  in
    match uu____7588 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7636 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7636 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                    | (FStar_Pervasives_Native.None ,uu____7822) -> def
                    | (uu____7833,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7845) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _7861  ->
                                  FStar_Syntax_Syntax.U_name _7861))
=======
=======
>>>>>>> snap
                    | (FStar_Pervasives_Native.None ,uu____7799) -> def
                    | (uu____7810,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7822) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _7838  ->
                                  FStar_Syntax_Syntax.U_name _7838))
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
            let uu____7943 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7943 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7978 ->
            let t' = arrow binders c  in
            let uu____7990 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____7990 with
             | (uvs1,t'1) ->
                 let uu____8011 =
                   let uu____8012 = FStar_Syntax_Subst.compress t'1  in
                   uu____8012.FStar_Syntax_Syntax.n  in
                 (match uu____8011 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8061 -> failwith "Impossible"))
=======
=======
>>>>>>> snap
            let uu____7920 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7920 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7955 ->
            let t' = arrow binders c  in
            let uu____7967 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____7967 with
             | (uvs1,t'1) ->
                 let uu____7988 =
                   let uu____7989 = FStar_Syntax_Subst.compress t'1  in
                   uu____7989.FStar_Syntax_Syntax.n  in
                 (match uu____7988 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8038 -> failwith "Impossible"))
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____8086 -> false
=======
    | uu____8063 -> false
>>>>>>> snap
=======
    | uu____8063 -> false
>>>>>>> snap
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____8097 -> false
=======
    | uu____8074 -> false
>>>>>>> snap
=======
    | uu____8074 -> false
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____8160 =
        let uu____8161 = pre_typ t  in uu____8161.FStar_Syntax_Syntax.n  in
      match uu____8160 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8166 -> false
=======
      let uu____8137 =
        let uu____8138 = pre_typ t  in uu____8138.FStar_Syntax_Syntax.n  in
      match uu____8137 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8143 -> false
>>>>>>> snap
=======
      let uu____8137 =
        let uu____8138 = pre_typ t  in uu____8138.FStar_Syntax_Syntax.n  in
      match uu____8137 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8143 -> false
>>>>>>> snap
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____8180 =
        let uu____8181 = pre_typ t  in uu____8181.FStar_Syntax_Syntax.n  in
      match uu____8180 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8185 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8187) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8213) ->
          is_constructed_typ t1 lid
      | uu____8218 -> false
=======
      let uu____8157 =
        let uu____8158 = pre_typ t  in uu____8158.FStar_Syntax_Syntax.n  in
      match uu____8157 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8162 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8164) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8190) ->
          is_constructed_typ t1 lid
      | uu____8195 -> false
>>>>>>> snap
=======
      let uu____8157 =
        let uu____8158 = pre_typ t  in uu____8158.FStar_Syntax_Syntax.n  in
      match uu____8157 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8162 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8164) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8190) ->
          is_constructed_typ t1 lid
      | uu____8195 -> false
>>>>>>> snap
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_bvar uu____8231 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8232 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8233 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8235) -> get_tycon t2
    | uu____8260 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8268 =
      let uu____8269 = un_uinst t  in uu____8269.FStar_Syntax_Syntax.n  in
    match uu____8268 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8274 -> false
=======
=======
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_bvar uu____8208 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8209 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8210 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8212) -> get_tycon t2
    | uu____8237 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8245 =
      let uu____8246 = un_uinst t  in uu____8246.FStar_Syntax_Syntax.n  in
    match uu____8245 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8251 -> false
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____8288 =
        let uu____8292 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8292  in
      match uu____8288 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8324 -> false
=======
=======
>>>>>>> snap
      let uu____8265 =
        let uu____8269 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8269  in
      match uu____8265 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8301 -> false
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
  fun uu____8343  ->
    let u =
      let uu____8349 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _8366  -> FStar_Syntax_Syntax.U_unif _8366)
        uu____8349
       in
    let uu____8367 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8367, u)
=======
  fun uu____8320  ->
    let u =
      let uu____8326 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _8343  -> FStar_Syntax_Syntax.U_unif _8343)
        uu____8326
       in
    let uu____8344 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8344, u)
>>>>>>> snap
=======
  fun uu____8320  ->
    let u =
      let uu____8326 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _8343  -> FStar_Syntax_Syntax.U_unif _8343)
        uu____8326
       in
    let uu____8344 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8344, u)
>>>>>>> snap
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____8380 = eq_tm a a'  in
      match uu____8380 with | Equal  -> true | uu____8383 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8388 =
    let uu____8395 =
      let uu____8396 =
        let uu____8397 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8397
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8396  in
    FStar_Syntax_Syntax.mk uu____8395  in
  uu____8388 FStar_Pervasives_Native.None FStar_Range.dummyRange 
=======
=======
>>>>>>> snap
      let uu____8357 = eq_tm a a'  in
      match uu____8357 with | Equal  -> true | uu____8360 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8365 =
    let uu____8372 =
      let uu____8373 =
        let uu____8374 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8374
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8373  in
    FStar_Syntax_Syntax.mk uu____8372  in
  uu____8365 FStar_Pervasives_Native.None FStar_Range.dummyRange 
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____8509 =
            let uu____8512 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8513 =
              let uu____8520 =
                let uu____8521 =
                  let uu____8538 =
                    let uu____8549 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8558 =
                      let uu____8569 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8569]  in
                    uu____8549 :: uu____8558  in
                  (tand, uu____8538)  in
                FStar_Syntax_Syntax.Tm_app uu____8521  in
              FStar_Syntax_Syntax.mk uu____8520  in
            uu____8513 FStar_Pervasives_Native.None uu____8512  in
          FStar_Pervasives_Native.Some uu____8509
=======
          let uu____8486 =
            let uu____8489 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
=======
          let uu____8486 =
            let uu____8489 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
>>>>>>> snap
            let uu____8490 =
              let uu____8497 =
                let uu____8498 =
                  let uu____8515 =
                    let uu____8526 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8535 =
                      let uu____8546 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8546]  in
                    uu____8526 :: uu____8535  in
                  (tand, uu____8515)  in
                FStar_Syntax_Syntax.Tm_app uu____8498  in
              FStar_Syntax_Syntax.mk uu____8497  in
            uu____8490 FStar_Pervasives_Native.None uu____8489  in
          FStar_Pervasives_Native.Some uu____8486
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____8646 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8647 =
          let uu____8654 =
            let uu____8655 =
              let uu____8672 =
                let uu____8683 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8692 =
                  let uu____8703 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8703]  in
                uu____8683 :: uu____8692  in
              (op_t, uu____8672)  in
            FStar_Syntax_Syntax.Tm_app uu____8655  in
          FStar_Syntax_Syntax.mk uu____8654  in
        uu____8647 FStar_Pervasives_Native.None uu____8646
=======
        let uu____8623 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
=======
        let uu____8623 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
>>>>>>> snap
        let uu____8624 =
          let uu____8631 =
            let uu____8632 =
              let uu____8649 =
                let uu____8660 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8669 =
                  let uu____8680 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8680]  in
                uu____8660 :: uu____8669  in
              (op_t, uu____8649)  in
            FStar_Syntax_Syntax.Tm_app uu____8632  in
          FStar_Syntax_Syntax.mk uu____8631  in
        uu____8624 FStar_Pervasives_Native.None uu____8623
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____8760 =
      let uu____8767 =
        let uu____8768 =
          let uu____8785 =
            let uu____8796 = FStar_Syntax_Syntax.as_arg phi  in [uu____8796]
             in
          (t_not, uu____8785)  in
        FStar_Syntax_Syntax.Tm_app uu____8768  in
      FStar_Syntax_Syntax.mk uu____8767  in
    uu____8760 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
=======
=======
>>>>>>> snap
    let uu____8737 =
      let uu____8744 =
        let uu____8745 =
          let uu____8762 =
            let uu____8773 = FStar_Syntax_Syntax.as_arg phi  in [uu____8773]
             in
          (t_not, uu____8762)  in
        FStar_Syntax_Syntax.Tm_app uu____8745  in
      FStar_Syntax_Syntax.mk uu____8744  in
    uu____8737 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____8993 =
      let uu____9000 =
        let uu____9001 =
          let uu____9018 =
            let uu____9029 = FStar_Syntax_Syntax.as_arg e  in [uu____9029]
             in
          (b2t_v, uu____9018)  in
        FStar_Syntax_Syntax.Tm_app uu____9001  in
      FStar_Syntax_Syntax.mk uu____9000  in
    uu____8993 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
=======
    let uu____8970 =
      let uu____8977 =
        let uu____8978 =
          let uu____8995 =
            let uu____9006 = FStar_Syntax_Syntax.as_arg e  in [uu____9006]
             in
=======
    let uu____8970 =
      let uu____8977 =
        let uu____8978 =
          let uu____8995 =
            let uu____9006 = FStar_Syntax_Syntax.as_arg e  in [uu____9006]
             in
>>>>>>> snap
          (b2t_v, uu____8995)  in
        FStar_Syntax_Syntax.Tm_app uu____8978  in
      FStar_Syntax_Syntax.mk uu____8977  in
    uu____8970 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____9076 = head_and_args e  in
    match uu____9076 with
    | (hd1,args) ->
        let uu____9121 =
          let uu____9136 =
            let uu____9137 = FStar_Syntax_Subst.compress hd1  in
            uu____9137.FStar_Syntax_Syntax.n  in
          (uu____9136, args)  in
        (match uu____9121 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9154)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9189 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9211 =
      let uu____9212 = unmeta t  in uu____9212.FStar_Syntax_Syntax.n  in
    match uu____9211 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9217 -> false
=======
    let uu____9053 = head_and_args e  in
    match uu____9053 with
    | (hd1,args) ->
        let uu____9098 =
          let uu____9113 =
            let uu____9114 = FStar_Syntax_Subst.compress hd1  in
            uu____9114.FStar_Syntax_Syntax.n  in
          (uu____9113, args)  in
        (match uu____9098 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9131)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9166 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9188 =
      let uu____9189 = unmeta t  in uu____9189.FStar_Syntax_Syntax.n  in
    match uu____9188 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9194 -> false
>>>>>>> snap
=======
    let uu____9053 = head_and_args e  in
    match uu____9053 with
    | (hd1,args) ->
        let uu____9098 =
          let uu____9113 =
            let uu____9114 = FStar_Syntax_Subst.compress hd1  in
            uu____9114.FStar_Syntax_Syntax.n  in
          (uu____9113, args)  in
        (match uu____9098 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9131)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9166 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9188 =
      let uu____9189 = unmeta t  in uu____9189.FStar_Syntax_Syntax.n  in
    match uu____9188 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9194 -> false
>>>>>>> snap
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____9240 = is_t_true t1  in
      if uu____9240
      then t2
      else
        (let uu____9247 = is_t_true t2  in
         if uu____9247 then t1 else mk_conj t1 t2)
=======
      let uu____9217 = is_t_true t1  in
      if uu____9217
      then t2
      else
        (let uu____9224 = is_t_true t2  in
         if uu____9224 then t1 else mk_conj t1 t2)
>>>>>>> snap
=======
      let uu____9217 = is_t_true t1  in
      if uu____9217
      then t2
      else
        (let uu____9224 = is_t_true t2  in
         if uu____9224 then t1 else mk_conj t1 t2)
>>>>>>> snap
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____9275 = is_t_true t1  in
      if uu____9275
      then t_true
      else
        (let uu____9282 = is_t_true t2  in
         if uu____9282 then t_true else mk_disj t1 t2)
=======
=======
>>>>>>> snap
      let uu____9252 = is_t_true t1  in
      if uu____9252
      then t_true
      else
        (let uu____9259 = is_t_true t2  in
         if uu____9259 then t_true else mk_disj t1 t2)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____9311 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9312 =
        let uu____9319 =
          let uu____9320 =
            let uu____9337 =
              let uu____9348 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9357 =
                let uu____9368 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9368]  in
              uu____9348 :: uu____9357  in
            (teq, uu____9337)  in
          FStar_Syntax_Syntax.Tm_app uu____9320  in
        FStar_Syntax_Syntax.mk uu____9319  in
      uu____9312 FStar_Pervasives_Native.None uu____9311
=======
      let uu____9288 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
=======
      let uu____9288 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
>>>>>>> snap
      let uu____9289 =
        let uu____9296 =
          let uu____9297 =
            let uu____9314 =
              let uu____9325 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9334 =
                let uu____9345 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9345]  in
              uu____9325 :: uu____9334  in
            (teq, uu____9314)  in
          FStar_Syntax_Syntax.Tm_app uu____9297  in
        FStar_Syntax_Syntax.mk uu____9296  in
      uu____9289 FStar_Pervasives_Native.None uu____9288
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____9435 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9436 =
            let uu____9443 =
              let uu____9444 =
                let uu____9461 =
                  let uu____9472 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9481 =
                    let uu____9492 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9501 =
                      let uu____9512 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9512]  in
                    uu____9492 :: uu____9501  in
                  uu____9472 :: uu____9481  in
                (eq_inst, uu____9461)  in
              FStar_Syntax_Syntax.Tm_app uu____9444  in
            FStar_Syntax_Syntax.mk uu____9443  in
          uu____9436 FStar_Pervasives_Native.None uu____9435
=======
          let uu____9412 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
=======
          let uu____9412 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
>>>>>>> snap
          let uu____9413 =
            let uu____9420 =
              let uu____9421 =
                let uu____9438 =
                  let uu____9449 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9458 =
                    let uu____9469 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9478 =
                      let uu____9489 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9489]  in
                    uu____9469 :: uu____9478  in
                  uu____9449 :: uu____9458  in
                (eq_inst, uu____9438)  in
              FStar_Syntax_Syntax.Tm_app uu____9421  in
            FStar_Syntax_Syntax.mk uu____9420  in
          uu____9413 FStar_Pervasives_Native.None uu____9412
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____9589 =
          let uu____9596 =
            let uu____9597 =
              let uu____9614 =
                let uu____9625 = FStar_Syntax_Syntax.iarg t  in
                let uu____9634 =
                  let uu____9645 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9654 =
                    let uu____9665 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9665]  in
                  uu____9645 :: uu____9654  in
                uu____9625 :: uu____9634  in
              (t_has_type1, uu____9614)  in
            FStar_Syntax_Syntax.Tm_app uu____9597  in
          FStar_Syntax_Syntax.mk uu____9596  in
        uu____9589 FStar_Pervasives_Native.None FStar_Range.dummyRange
=======
=======
>>>>>>> snap
        let uu____9566 =
          let uu____9573 =
            let uu____9574 =
              let uu____9591 =
                let uu____9602 = FStar_Syntax_Syntax.iarg t  in
                let uu____9611 =
                  let uu____9622 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9631 =
                    let uu____9642 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9642]  in
                  uu____9622 :: uu____9631  in
                uu____9602 :: uu____9611  in
              (t_has_type1, uu____9591)  in
            FStar_Syntax_Syntax.Tm_app uu____9574  in
          FStar_Syntax_Syntax.mk uu____9573  in
        uu____9566 FStar_Pervasives_Native.None FStar_Range.dummyRange
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____9742 =
          let uu____9749 =
            let uu____9750 =
              let uu____9767 =
                let uu____9778 = FStar_Syntax_Syntax.iarg t  in
                let uu____9787 =
                  let uu____9798 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9798]  in
                uu____9778 :: uu____9787  in
              (t_with_type1, uu____9767)  in
            FStar_Syntax_Syntax.Tm_app uu____9750  in
          FStar_Syntax_Syntax.mk uu____9749  in
        uu____9742 FStar_Pervasives_Native.None FStar_Range.dummyRange
=======
=======
>>>>>>> snap
        let uu____9719 =
          let uu____9726 =
            let uu____9727 =
              let uu____9744 =
                let uu____9755 = FStar_Syntax_Syntax.iarg t  in
                let uu____9764 =
                  let uu____9775 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9775]  in
                uu____9755 :: uu____9764  in
              (t_with_type1, uu____9744)  in
            FStar_Syntax_Syntax.Tm_app uu____9727  in
          FStar_Syntax_Syntax.mk uu____9726  in
        uu____9719 FStar_Pervasives_Native.None FStar_Range.dummyRange
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
<<<<<<< HEAD
<<<<<<< HEAD
  let uu____9845 =
    let uu____9852 =
      let uu____9853 =
        let uu____9860 =
=======
=======
>>>>>>> snap
  let uu____9822 =
    let uu____9829 =
      let uu____9830 =
        let uu____9837 =
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
<<<<<<< HEAD
<<<<<<< HEAD
        (uu____9860, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9853  in
    FStar_Syntax_Syntax.mk uu____9852  in
  uu____9845 FStar_Pervasives_Native.None FStar_Range.dummyRange 
=======
=======
>>>>>>> snap
        (uu____9837, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9830  in
    FStar_Syntax_Syntax.mk uu____9829  in
  uu____9822 FStar_Pervasives_Native.None FStar_Range.dummyRange 
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
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
  
<<<<<<< HEAD
=======
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.lcomp) =
  fun c0  ->
    let uu____9852 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____9865 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____9876 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____9852 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____9897  -> c0)
  
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____9943 =
          let uu____9950 =
            let uu____9951 =
              let uu____9968 =
                let uu____9979 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____9988 =
                  let uu____9999 =
                    let uu____10008 =
                      let uu____10009 =
                        let uu____10010 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10010]  in
                      abs uu____10009 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10008  in
                  [uu____9999]  in
                uu____9979 :: uu____9988  in
              (fa, uu____9968)  in
            FStar_Syntax_Syntax.Tm_app uu____9951  in
          FStar_Syntax_Syntax.mk uu____9950  in
        uu____9943 FStar_Pervasives_Native.None FStar_Range.dummyRange
=======
=======
>>>>>>> snap
        let uu____9980 =
          let uu____9987 =
            let uu____9988 =
              let uu____10005 =
                let uu____10016 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____10025 =
                  let uu____10036 =
                    let uu____10045 =
                      let uu____10046 =
                        let uu____10047 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10047]  in
                      abs uu____10046 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10045  in
                  [uu____10036]  in
                uu____10016 :: uu____10025  in
              (fa, uu____10005)  in
            FStar_Syntax_Syntax.Tm_app uu____9988  in
          FStar_Syntax_Syntax.mk uu____9987  in
        uu____9980 FStar_Pervasives_Native.None FStar_Range.dummyRange
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
             let uu____10137 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10137
=======
             let uu____10174 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10174
>>>>>>> snap
=======
             let uu____10174 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10174
>>>>>>> snap
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Pat_wild uu____10156 -> true
    | uu____10158 -> false
=======
    | FStar_Syntax_Syntax.Pat_wild uu____10193 -> true
    | uu____10195 -> false
>>>>>>> snap
=======
    | FStar_Syntax_Syntax.Pat_wild uu____10193 -> true
    | uu____10195 -> false
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____10205 =
=======
          let uu____10242 =
>>>>>>> snap
=======
          let uu____10242 =
>>>>>>> snap
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
<<<<<<< HEAD
<<<<<<< HEAD
          (uu____10205, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10234 =
=======
          (uu____10242, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10271 =
>>>>>>> snap
=======
          (uu____10242, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10271 =
>>>>>>> snap
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
<<<<<<< HEAD
<<<<<<< HEAD
          (uu____10234, FStar_Pervasives_Native.None, t2)  in
        let uu____10248 =
          let uu____10249 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10249  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10248
=======
=======
>>>>>>> snap
          (uu____10271, FStar_Pervasives_Native.None, t2)  in
        let uu____10285 =
          let uu____10286 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10286  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10285
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____10325 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10328 =
        let uu____10339 = FStar_Syntax_Syntax.as_arg p  in [uu____10339]  in
      mk_app uu____10325 uu____10328
=======
=======
>>>>>>> snap
      let uu____10362 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10365 =
        let uu____10376 = FStar_Syntax_Syntax.as_arg p  in [uu____10376]  in
      mk_app uu____10362 uu____10365
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____10379 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10382 =
        let uu____10393 = FStar_Syntax_Syntax.as_arg p  in [uu____10393]  in
      mk_app uu____10379 uu____10382
=======
=======
>>>>>>> snap
      let uu____10416 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10419 =
        let uu____10430 = FStar_Syntax_Syntax.as_arg p  in [uu____10430]  in
      mk_app uu____10416 uu____10419
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____10428 = head_and_args t  in
    match uu____10428 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____10477 =
          let uu____10492 =
            let uu____10493 = FStar_Syntax_Subst.compress head3  in
            uu____10493.FStar_Syntax_Syntax.n  in
          (uu____10492, args)  in
        (match uu____10477 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10512)::[]) when
=======
    let uu____10465 = head_and_args t  in
    match uu____10465 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
=======
    let uu____10465 = head_and_args t  in
    match uu____10465 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
>>>>>>> snap
        let uu____10514 =
          let uu____10529 =
            let uu____10530 = FStar_Syntax_Subst.compress head3  in
            uu____10530.FStar_Syntax_Syntax.n  in
          (uu____10529, args)  in
        (match uu____10514 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10549)::[]) when
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
<<<<<<< HEAD
<<<<<<< HEAD
                  let uu____10578 =
                    let uu____10583 =
                      let uu____10584 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10584]  in
                    FStar_Syntax_Subst.open_term uu____10583 p  in
                  (match uu____10578 with
=======
=======
>>>>>>> snap
                  let uu____10615 =
                    let uu____10620 =
                      let uu____10621 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10621]  in
                    FStar_Syntax_Subst.open_term uu____10620 p  in
                  (match uu____10615 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
<<<<<<< HEAD
<<<<<<< HEAD
                         | uu____10641 -> failwith "impossible"  in
                       let uu____10649 =
                         let uu____10651 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10651
                          in
                       if uu____10649
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10667 -> FStar_Pervasives_Native.None)
         | uu____10670 -> FStar_Pervasives_Native.None)
=======
=======
>>>>>>> snap
                         | uu____10678 -> failwith "impossible"  in
                       let uu____10686 =
                         let uu____10688 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10688
                          in
                       if uu____10686
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10704 -> FStar_Pervasives_Native.None)
         | uu____10707 -> FStar_Pervasives_Native.None)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____10701 = head_and_args t  in
    match uu____10701 with
    | (head1,args) ->
        let uu____10752 =
          let uu____10767 =
            let uu____10768 = FStar_Syntax_Subst.compress head1  in
            uu____10768.FStar_Syntax_Syntax.n  in
          (uu____10767, args)  in
        (match uu____10752 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10790;
               FStar_Syntax_Syntax.vars = uu____10791;_},u::[]),(t1,uu____10794)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10841 -> FStar_Pervasives_Native.None)
=======
    let uu____10738 = head_and_args t  in
    match uu____10738 with
    | (head1,args) ->
        let uu____10789 =
          let uu____10804 =
            let uu____10805 = FStar_Syntax_Subst.compress head1  in
            uu____10805.FStar_Syntax_Syntax.n  in
          (uu____10804, args)  in
        (match uu____10789 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10827;
               FStar_Syntax_Syntax.vars = uu____10828;_},u::[]),(t1,uu____10831)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10878 -> FStar_Pervasives_Native.None)
>>>>>>> snap
=======
    let uu____10738 = head_and_args t  in
    match uu____10738 with
    | (head1,args) ->
        let uu____10789 =
          let uu____10804 =
            let uu____10805 = FStar_Syntax_Subst.compress head1  in
            uu____10805.FStar_Syntax_Syntax.n  in
          (uu____10804, args)  in
        (match uu____10789 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10827;
               FStar_Syntax_Syntax.vars = uu____10828;_},u::[]),(t1,uu____10831)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10878 -> FStar_Pervasives_Native.None)
>>>>>>> snap
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____10876 = head_and_args t  in
    match uu____10876 with
    | (head1,args) ->
        let uu____10927 =
          let uu____10942 =
            let uu____10943 = FStar_Syntax_Subst.compress head1  in
            uu____10943.FStar_Syntax_Syntax.n  in
          (uu____10942, args)  in
        (match uu____10927 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10965;
               FStar_Syntax_Syntax.vars = uu____10966;_},u::[]),(t1,uu____10969)::[])
=======
    let uu____10913 = head_and_args t  in
    match uu____10913 with
    | (head1,args) ->
        let uu____10964 =
          let uu____10979 =
            let uu____10980 = FStar_Syntax_Subst.compress head1  in
            uu____10980.FStar_Syntax_Syntax.n  in
          (uu____10979, args)  in
        (match uu____10964 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____11002;
               FStar_Syntax_Syntax.vars = uu____11003;_},u::[]),(t1,uu____11006)::[])
>>>>>>> snap
=======
    let uu____10913 = head_and_args t  in
    match uu____10913 with
    | (head1,args) ->
        let uu____10964 =
          let uu____10979 =
            let uu____10980 = FStar_Syntax_Subst.compress head1  in
            uu____10980.FStar_Syntax_Syntax.n  in
          (uu____10979, args)  in
        (match uu____10964 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____11002;
               FStar_Syntax_Syntax.vars = uu____11003;_},u::[]),(t1,uu____11006)::[])
>>>>>>> snap
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
<<<<<<< HEAD
<<<<<<< HEAD
         | uu____11016 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11044 =
      let uu____11061 = unmeta t  in head_and_args uu____11061  in
    match uu____11044 with
    | (head1,uu____11064) ->
        let uu____11089 =
          let uu____11090 = un_uinst head1  in
          uu____11090.FStar_Syntax_Syntax.n  in
        (match uu____11089 with
=======
         | uu____11053 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
=======
         | uu____11053 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
>>>>>>> snap
    let uu____11081 =
      let uu____11098 = unmeta t  in head_and_args uu____11098  in
    match uu____11081 with
    | (head1,uu____11101) ->
        let uu____11126 =
          let uu____11127 = un_uinst head1  in
          uu____11127.FStar_Syntax_Syntax.n  in
        (match uu____11126 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
         | uu____11095 -> false)
=======
         | uu____11132 -> false)
>>>>>>> snap
=======
         | uu____11132 -> false)
>>>>>>> snap
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____11115 =
      let uu____11128 =
        let uu____11129 = FStar_Syntax_Subst.compress t  in
        uu____11129.FStar_Syntax_Syntax.n  in
      match uu____11128 with
=======
=======
>>>>>>> snap
    let uu____11152 =
      let uu____11165 =
        let uu____11166 = FStar_Syntax_Subst.compress t  in
        uu____11166.FStar_Syntax_Syntax.n  in
      match uu____11165 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____11259 =
            let uu____11270 =
              let uu____11271 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____11271  in
            (b, uu____11270)  in
          FStar_Pervasives_Native.Some uu____11259
      | uu____11288 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____11115
      (fun uu____11326  ->
         match uu____11326 with
         | (b,c) ->
             let uu____11363 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11363 with
=======
=======
>>>>>>> snap
          let uu____11296 =
            let uu____11307 =
              let uu____11308 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____11308  in
            (b, uu____11307)  in
          FStar_Pervasives_Native.Some uu____11296
      | uu____11325 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____11152
      (fun uu____11363  ->
         match uu____11363 with
         | (b,c) ->
             let uu____11400 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11400 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
<<<<<<< HEAD
<<<<<<< HEAD
                    | uu____11426 ->
=======
                    | uu____11463 ->
>>>>>>> snap
=======
                    | uu____11463 ->
>>>>>>> snap
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____11463 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11463
=======
      let uu____11500 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11500
>>>>>>> snap
=======
      let uu____11500 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11500
>>>>>>> snap
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | QAll _0 -> true | uu____11515 -> false
=======
    match projectee with | QAll _0 -> true | uu____11552 -> false
>>>>>>> snap
=======
    match projectee with | QAll _0 -> true | uu____11552 -> false
>>>>>>> snap
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | QEx _0 -> true | uu____11558 -> false
=======
    match projectee with | QEx _0 -> true | uu____11595 -> false
>>>>>>> snap
=======
    match projectee with | QEx _0 -> true | uu____11595 -> false
>>>>>>> snap
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | BaseConn _0 -> true | uu____11599 -> false
=======
    match projectee with | BaseConn _0 -> true | uu____11636 -> false
>>>>>>> snap
=======
    match projectee with | BaseConn _0 -> true | uu____11636 -> false
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11985) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11997) ->
          unmeta_monadic t
      | uu____12010 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12079 =
        match uu____12079 with
=======
          (t,FStar_Syntax_Syntax.Meta_monadic uu____12022) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____12034) ->
          unmeta_monadic t
      | uu____12047 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12116 =
        match uu____12116 with
>>>>>>> snap
=======
          (t,FStar_Syntax_Syntax.Meta_monadic uu____12022) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____12034) ->
          unmeta_monadic t
      | uu____12047 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12116 =
        match uu____12116 with
>>>>>>> snap
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
<<<<<<< HEAD
<<<<<<< HEAD
                (fun uu____12117  ->
                   match uu____12117 with
                   | (lid,out_lid) ->
                       let uu____12126 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12126
=======
=======
>>>>>>> snap
                (fun uu____12154  ->
                   match uu____12154 with
                   | (lid,out_lid) ->
                       let uu____12163 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12163
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____12153 = head_and_args t  in
      match uu____12153 with
      | (hd1,args) ->
          let uu____12198 =
            let uu____12199 = un_uinst hd1  in
            uu____12199.FStar_Syntax_Syntax.n  in
          (match uu____12198 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12205 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12214 = un_squash t  in
      FStar_Util.bind_opt uu____12214
        (fun t1  ->
           let uu____12230 = head_and_args' t1  in
           match uu____12230 with
           | (hd1,args) ->
               let uu____12269 =
                 let uu____12270 = un_uinst hd1  in
                 uu____12270.FStar_Syntax_Syntax.n  in
               (match uu____12269 with
=======
      let uu____12190 = head_and_args t  in
      match uu____12190 with
      | (hd1,args) ->
          let uu____12235 =
            let uu____12236 = un_uinst hd1  in
            uu____12236.FStar_Syntax_Syntax.n  in
          (match uu____12235 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12242 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12251 = un_squash t  in
      FStar_Util.bind_opt uu____12251
        (fun t1  ->
           let uu____12267 = head_and_args' t1  in
           match uu____12267 with
           | (hd1,args) ->
=======
      let uu____12190 = head_and_args t  in
      match uu____12190 with
      | (hd1,args) ->
          let uu____12235 =
            let uu____12236 = un_uinst hd1  in
            uu____12236.FStar_Syntax_Syntax.n  in
          (match uu____12235 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12242 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12251 = un_squash t  in
      FStar_Util.bind_opt uu____12251
        (fun t1  ->
           let uu____12267 = head_and_args' t1  in
           match uu____12267 with
           | (hd1,args) ->
>>>>>>> snap
               let uu____12306 =
                 let uu____12307 = un_uinst hd1  in
                 uu____12307.FStar_Syntax_Syntax.n  in
               (match uu____12306 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
<<<<<<< HEAD
<<<<<<< HEAD
                | uu____12276 -> FStar_Pervasives_Native.None))
=======
                | uu____12313 -> FStar_Pervasives_Native.None))
>>>>>>> snap
=======
                | uu____12313 -> FStar_Pervasives_Native.None))
>>>>>>> snap
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
<<<<<<< HEAD
<<<<<<< HEAD
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12317,pats)) ->
          let uu____12355 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12355)
      | uu____12368 -> ([], t1)  in
=======
=======
>>>>>>> snap
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12354,pats)) ->
          let uu____12392 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12392)
      | uu____12405 -> ([], t1)  in
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____12435 = head_and_args t1  in
        match uu____12435 with
        | (t2,args) ->
            let uu____12490 = un_uinst t2  in
            let uu____12491 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12532  ->
                      match uu____12532 with
                      | (t3,imp) ->
                          let uu____12551 = unascribe t3  in
                          (uu____12551, imp)))
               in
            (uu____12490, uu____12491)
         in
      let rec aux qopt out t1 =
        let uu____12602 = let uu____12626 = flat t1  in (qopt, uu____12626)
           in
        match uu____12602 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12666;
                 FStar_Syntax_Syntax.vars = uu____12667;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12670);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12671;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12672;_},uu____12673)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12775;
                 FStar_Syntax_Syntax.vars = uu____12776;_},uu____12777::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12780);
                  FStar_Syntax_Syntax.pos = uu____12781;
                  FStar_Syntax_Syntax.vars = uu____12782;_},uu____12783)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12900;
               FStar_Syntax_Syntax.vars = uu____12901;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12904);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12905;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12906;_},uu____12907)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13000 =
              let uu____13004 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13004  in
            aux uu____13000 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13014;
               FStar_Syntax_Syntax.vars = uu____13015;_},uu____13016::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____13019);
                FStar_Syntax_Syntax.pos = uu____13020;
                FStar_Syntax_Syntax.vars = uu____13021;_},uu____13022)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13131 =
              let uu____13135 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13135  in
            aux uu____13131 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13145) ->
            let bs = FStar_List.rev out  in
            let uu____13198 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13198 with
             | (bs1,t2) ->
                 let uu____13207 = patterns t2  in
                 (match uu____13207 with
=======
        let uu____12472 = head_and_args t1  in
        match uu____12472 with
        | (t2,args) ->
            let uu____12527 = un_uinst t2  in
            let uu____12528 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12569  ->
                      match uu____12569 with
                      | (t3,imp) ->
                          let uu____12588 = unascribe t3  in
                          (uu____12588, imp)))
               in
            (uu____12527, uu____12528)
         in
      let rec aux qopt out t1 =
        let uu____12639 = let uu____12663 = flat t1  in (qopt, uu____12663)
           in
        match uu____12639 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12703;
                 FStar_Syntax_Syntax.vars = uu____12704;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12707);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12708;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12709;_},uu____12710)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12812;
                 FStar_Syntax_Syntax.vars = uu____12813;_},uu____12814::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12817);
                  FStar_Syntax_Syntax.pos = uu____12818;
                  FStar_Syntax_Syntax.vars = uu____12819;_},uu____12820)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12937;
               FStar_Syntax_Syntax.vars = uu____12938;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12941);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12942;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12943;_},uu____12944)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13037 =
              let uu____13041 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13041  in
            aux uu____13037 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13051;
               FStar_Syntax_Syntax.vars = uu____13052;_},uu____13053::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____13056);
                FStar_Syntax_Syntax.pos = uu____13057;
                FStar_Syntax_Syntax.vars = uu____13058;_},uu____13059)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13168 =
              let uu____13172 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13172  in
            aux uu____13168 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13182) ->
            let bs = FStar_List.rev out  in
            let uu____13235 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13235 with
             | (bs1,t2) ->
                 let uu____13244 = patterns t2  in
                 (match uu____13244 with
>>>>>>> snap
=======
        let uu____12472 = head_and_args t1  in
        match uu____12472 with
        | (t2,args) ->
            let uu____12527 = un_uinst t2  in
            let uu____12528 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12569  ->
                      match uu____12569 with
                      | (t3,imp) ->
                          let uu____12588 = unascribe t3  in
                          (uu____12588, imp)))
               in
            (uu____12527, uu____12528)
         in
      let rec aux qopt out t1 =
        let uu____12639 = let uu____12663 = flat t1  in (qopt, uu____12663)
           in
        match uu____12639 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12703;
                 FStar_Syntax_Syntax.vars = uu____12704;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12707);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12708;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12709;_},uu____12710)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12812;
                 FStar_Syntax_Syntax.vars = uu____12813;_},uu____12814::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12817);
                  FStar_Syntax_Syntax.pos = uu____12818;
                  FStar_Syntax_Syntax.vars = uu____12819;_},uu____12820)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12937;
               FStar_Syntax_Syntax.vars = uu____12938;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12941);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12942;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12943;_},uu____12944)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13037 =
              let uu____13041 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13041  in
            aux uu____13037 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13051;
               FStar_Syntax_Syntax.vars = uu____13052;_},uu____13053::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____13056);
                FStar_Syntax_Syntax.pos = uu____13057;
                FStar_Syntax_Syntax.vars = uu____13058;_},uu____13059)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13168 =
              let uu____13172 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13172  in
            aux uu____13168 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13182) ->
            let bs = FStar_List.rev out  in
            let uu____13235 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13235 with
             | (bs1,t2) ->
                 let uu____13244 = patterns t2  in
                 (match uu____13244 with
>>>>>>> snap
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
<<<<<<< HEAD
<<<<<<< HEAD
        | uu____13257 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13312 = un_squash t  in
      FStar_Util.bind_opt uu____13312
        (fun t1  ->
           let uu____13327 = arrow_one t1  in
           match uu____13327 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13342 =
                 let uu____13344 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13344  in
               if uu____13342
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13354 = comp_to_comp_typ_nouniv c  in
                    uu____13354.FStar_Syntax_Syntax.result_typ  in
                  let uu____13355 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13355
                  then
                    let uu____13362 = patterns q  in
                    match uu____13362 with
=======
        | uu____13294 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13349 = un_squash t  in
      FStar_Util.bind_opt uu____13349
        (fun t1  ->
           let uu____13364 = arrow_one t1  in
           match uu____13364 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13379 =
                 let uu____13381 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13381  in
               if uu____13379
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13391 = comp_to_comp_typ_nouniv c  in
                    uu____13391.FStar_Syntax_Syntax.result_typ  in
                  let uu____13392 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13392
                  then
                    let uu____13399 = patterns q  in
                    match uu____13399 with
>>>>>>> snap
=======
        | uu____13294 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13349 = un_squash t  in
      FStar_Util.bind_opt uu____13349
        (fun t1  ->
           let uu____13364 = arrow_one t1  in
           match uu____13364 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13379 =
                 let uu____13381 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13381  in
               if uu____13379
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13391 = comp_to_comp_typ_nouniv c  in
                    uu____13391.FStar_Syntax_Syntax.result_typ  in
                  let uu____13392 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13392
                  then
                    let uu____13399 = patterns q  in
                    match uu____13399 with
>>>>>>> snap
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
<<<<<<< HEAD
<<<<<<< HEAD
                    (let uu____13425 =
                       let uu____13426 =
                         let uu____13431 =
                           let uu____13432 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13443 =
                             let uu____13454 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13454]  in
                           uu____13432 :: uu____13443  in
                         (FStar_Parser_Const.imp_lid, uu____13431)  in
                       BaseConn uu____13426  in
                     FStar_Pervasives_Native.Some uu____13425))
           | uu____13487 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13495 = un_squash t  in
      FStar_Util.bind_opt uu____13495
        (fun t1  ->
           let uu____13526 = head_and_args' t1  in
           match uu____13526 with
           | (hd1,args) ->
               let uu____13565 =
                 let uu____13580 =
                   let uu____13581 = un_uinst hd1  in
                   uu____13581.FStar_Syntax_Syntax.n  in
                 (uu____13580, args)  in
               (match uu____13565 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13598)::(a2,uu____13600)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13651 =
                      let uu____13652 = FStar_Syntax_Subst.compress a2  in
                      uu____13652.FStar_Syntax_Syntax.n  in
                    (match uu____13651 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13659) ->
                         let uu____13694 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13694 with
=======
=======
>>>>>>> snap
                    (let uu____13462 =
                       let uu____13463 =
                         let uu____13468 =
                           let uu____13469 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13480 =
                             let uu____13491 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13491]  in
                           uu____13469 :: uu____13480  in
                         (FStar_Parser_Const.imp_lid, uu____13468)  in
                       BaseConn uu____13463  in
                     FStar_Pervasives_Native.Some uu____13462))
           | uu____13524 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13532 = un_squash t  in
      FStar_Util.bind_opt uu____13532
        (fun t1  ->
           let uu____13563 = head_and_args' t1  in
           match uu____13563 with
           | (hd1,args) ->
               let uu____13602 =
                 let uu____13617 =
                   let uu____13618 = un_uinst hd1  in
                   uu____13618.FStar_Syntax_Syntax.n  in
                 (uu____13617, args)  in
               (match uu____13602 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13635)::(a2,uu____13637)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13688 =
                      let uu____13689 = FStar_Syntax_Subst.compress a2  in
                      uu____13689.FStar_Syntax_Syntax.n  in
                    (match uu____13688 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13696) ->
                         let uu____13731 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13731 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
<<<<<<< HEAD
<<<<<<< HEAD
                                | uu____13747 -> failwith "impossible"  in
                              let uu____13755 = patterns q1  in
                              (match uu____13755 with
=======
                                | uu____13784 -> failwith "impossible"  in
                              let uu____13792 = patterns q1  in
                              (match uu____13792 with
>>>>>>> snap
=======
                                | uu____13784 -> failwith "impossible"  in
                              let uu____13792 = patterns q1  in
                              (match uu____13792 with
>>>>>>> snap
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
<<<<<<< HEAD
<<<<<<< HEAD
                     | uu____13816 -> FStar_Pervasives_Native.None)
                | uu____13817 -> FStar_Pervasives_Native.None))
=======
                     | uu____13853 -> FStar_Pervasives_Native.None)
                | uu____13854 -> FStar_Pervasives_Native.None))
>>>>>>> snap
=======
                     | uu____13853 -> FStar_Pervasives_Native.None)
                | uu____13854 -> FStar_Pervasives_Native.None))
>>>>>>> snap
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____13840 = destruct_sq_forall phi  in
          (match uu____13840 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13850  -> FStar_Pervasives_Native.Some _13850)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13857 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13863 = destruct_sq_exists phi  in
          (match uu____13863 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13873  -> FStar_Pervasives_Native.Some _13873)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13880 -> f1)
      | uu____13883 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13887 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13887
      (fun uu____13892  ->
         let uu____13893 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13893
           (fun uu____13898  ->
              let uu____13899 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13899
                (fun uu____13904  ->
                   let uu____13905 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13905
                     (fun uu____13910  ->
                        let uu____13911 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13911
                          (fun uu____13915  -> FStar_Pervasives_Native.None)))))
=======
          let uu____13877 = destruct_sq_forall phi  in
          (match uu____13877 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13887  -> FStar_Pervasives_Native.Some _13887)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13894 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13900 = destruct_sq_exists phi  in
          (match uu____13900 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13910  -> FStar_Pervasives_Native.Some _13910)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13917 -> f1)
      | uu____13920 -> f1
     in
    let phi = unmeta_monadic f  in
=======
          let uu____13877 = destruct_sq_forall phi  in
          (match uu____13877 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13887  -> FStar_Pervasives_Native.Some _13887)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13894 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13900 = destruct_sq_exists phi  in
          (match uu____13900 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _13910  -> FStar_Pervasives_Native.Some _13910)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13917 -> f1)
      | uu____13920 -> f1
     in
    let phi = unmeta_monadic f  in
>>>>>>> snap
    let uu____13924 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13924
      (fun uu____13929  ->
         let uu____13930 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13930
           (fun uu____13935  ->
              let uu____13936 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13936
                (fun uu____13941  ->
                   let uu____13942 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13942
                     (fun uu____13947  ->
                        let uu____13948 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13948
                          (fun uu____13952  -> FStar_Pervasives_Native.None)))))
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____13933 =
            let uu____13938 =
=======
          let uu____13970 =
            let uu____13975 =
>>>>>>> snap
=======
          let uu____13970 =
            let uu____13975 =
>>>>>>> snap
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
<<<<<<< HEAD
<<<<<<< HEAD
            FStar_Util.Inr uu____13938  in
          let uu____13939 =
            let uu____13940 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13940  in
          let uu____13943 =
=======
=======
>>>>>>> snap
            FStar_Util.Inr uu____13975  in
          let uu____13976 =
            let uu____13977 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13977  in
          let uu____13980 =
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
<<<<<<< HEAD
<<<<<<< HEAD
            uu____13933 a.FStar_Syntax_Syntax.action_univs uu____13939
            FStar_Parser_Const.effect_Tot_lid uu____13943 [] pos
=======
            uu____13970 a.FStar_Syntax_Syntax.action_univs uu____13976
            FStar_Parser_Const.effect_Tot_lid uu____13980 [] pos
>>>>>>> snap
=======
            uu____13970 a.FStar_Syntax_Syntax.action_univs uu____13976
            FStar_Parser_Const.effect_Tot_lid uu____13980 [] pos
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____13969 =
      let uu____13976 =
        let uu____13977 =
          let uu____13994 =
            let uu____14005 = FStar_Syntax_Syntax.as_arg t  in [uu____14005]
             in
          (reify_1, uu____13994)  in
        FStar_Syntax_Syntax.Tm_app uu____13977  in
      FStar_Syntax_Syntax.mk uu____13976  in
    uu____13969 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
=======
    let uu____14006 =
      let uu____14013 =
        let uu____14014 =
          let uu____14031 =
            let uu____14042 = FStar_Syntax_Syntax.as_arg t  in [uu____14042]
             in
=======
    let uu____14006 =
      let uu____14013 =
        let uu____14014 =
          let uu____14031 =
            let uu____14042 = FStar_Syntax_Syntax.as_arg t  in [uu____14042]
             in
>>>>>>> snap
          (reify_1, uu____14031)  in
        FStar_Syntax_Syntax.Tm_app uu____14014  in
      FStar_Syntax_Syntax.mk uu____14013  in
    uu____14006 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____14057 =
        let uu____14064 =
          let uu____14065 =
            let uu____14066 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14066  in
          FStar_Syntax_Syntax.Tm_constant uu____14065  in
        FStar_Syntax_Syntax.mk uu____14064  in
      uu____14057 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14068 =
      let uu____14075 =
        let uu____14076 =
          let uu____14093 =
            let uu____14104 = FStar_Syntax_Syntax.as_arg t  in [uu____14104]
             in
          (reflect_, uu____14093)  in
        FStar_Syntax_Syntax.Tm_app uu____14076  in
      FStar_Syntax_Syntax.mk uu____14075  in
    uu____14068 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
=======
=======
>>>>>>> snap
      let uu____14094 =
        let uu____14101 =
          let uu____14102 =
            let uu____14103 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14103  in
          FStar_Syntax_Syntax.Tm_constant uu____14102  in
        FStar_Syntax_Syntax.mk uu____14101  in
      uu____14094 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14105 =
      let uu____14112 =
        let uu____14113 =
          let uu____14130 =
            let uu____14141 = FStar_Syntax_Syntax.as_arg t  in [uu____14141]
             in
          (reflect_, uu____14130)  in
        FStar_Syntax_Syntax.Tm_app uu____14113  in
      FStar_Syntax_Syntax.mk uu____14112  in
    uu____14105 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_delayed uu____14148 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14173 = unfold_lazy i  in delta_qualifier uu____14173
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14175 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14176 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14177 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14200 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14213 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14214 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14221 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14222 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14238) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14243;
           FStar_Syntax_Syntax.index = uu____14244;
           FStar_Syntax_Syntax.sort = t2;_},uu____14246)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14255) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14261,uu____14262) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14304) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14329,t2,uu____14331) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14356,t2) -> delta_qualifier t2
=======
=======
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_delayed uu____14185 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14210 = unfold_lazy i  in delta_qualifier uu____14210
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14212 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14213 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14214 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14237 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14250 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14251 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14258 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14259 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14275) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14280;
           FStar_Syntax_Syntax.index = uu____14281;
           FStar_Syntax_Syntax.sort = t2;_},uu____14283)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14292) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14298,uu____14299) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14341) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14366,t2,uu____14368) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14393,t2) -> delta_qualifier t2
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____14395 = delta_qualifier t  in incr_delta_depth uu____14395
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14403 =
      let uu____14404 = FStar_Syntax_Subst.compress t  in
      uu____14404.FStar_Syntax_Syntax.n  in
    match uu____14403 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14409 -> false
  
let rec apply_last :
  'Auu____14418 .
    ('Auu____14418 -> 'Auu____14418) ->
      'Auu____14418 Prims.list -> 'Auu____14418 Prims.list
=======
=======
>>>>>>> snap
    let uu____14432 = delta_qualifier t  in incr_delta_depth uu____14432
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14440 =
      let uu____14441 = FStar_Syntax_Subst.compress t  in
      uu____14441.FStar_Syntax_Syntax.n  in
    match uu____14440 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14446 -> false
  
let rec apply_last :
  'Auu____14455 .
    ('Auu____14455 -> 'Auu____14455) ->
      'Auu____14455 Prims.list -> 'Auu____14455 Prims.list
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
<<<<<<< HEAD
<<<<<<< HEAD
      | a::[] -> let uu____14444 = f a  in [uu____14444]
      | x::xs -> let uu____14449 = apply_last f xs  in x :: uu____14449
=======
      | a::[] -> let uu____14481 = f a  in [uu____14481]
      | x::xs -> let uu____14486 = apply_last f xs  in x :: uu____14486
>>>>>>> snap
=======
      | a::[] -> let uu____14481 = f a  in [uu____14481]
      | x::xs -> let uu____14486 = apply_last f xs  in x :: uu____14486
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____14504 =
            let uu____14511 =
              let uu____14512 =
=======
          let uu____14541 =
            let uu____14548 =
              let uu____14549 =
>>>>>>> snap
=======
          let uu____14541 =
            let uu____14548 =
              let uu____14549 =
>>>>>>> snap
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
<<<<<<< HEAD
<<<<<<< HEAD
              FStar_Syntax_Syntax.Tm_fvar uu____14512  in
            FStar_Syntax_Syntax.mk uu____14511  in
          uu____14504 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____14526 =
            let uu____14531 =
              let uu____14532 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14532
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14531 args  in
          uu____14526 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14546 =
            let uu____14551 =
              let uu____14552 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14552
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14551 args  in
          uu____14546 FStar_Pervasives_Native.None pos  in
        let uu____14553 =
          let uu____14554 =
            let uu____14555 = FStar_Syntax_Syntax.iarg typ  in [uu____14555]
             in
          nil uu____14554 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14589 =
                 let uu____14590 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14599 =
                   let uu____14610 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14619 =
                     let uu____14630 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14630]  in
                   uu____14610 :: uu____14619  in
                 uu____14590 :: uu____14599  in
               cons1 uu____14589 t.FStar_Syntax_Syntax.pos) l uu____14553
=======
=======
>>>>>>> snap
              FStar_Syntax_Syntax.Tm_fvar uu____14549  in
            FStar_Syntax_Syntax.mk uu____14548  in
          uu____14541 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____14563 =
            let uu____14568 =
              let uu____14569 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14569
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14568 args  in
          uu____14563 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14583 =
            let uu____14588 =
              let uu____14589 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14589
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14588 args  in
          uu____14583 FStar_Pervasives_Native.None pos  in
        let uu____14590 =
          let uu____14591 =
            let uu____14592 = FStar_Syntax_Syntax.iarg typ  in [uu____14592]
             in
          nil uu____14591 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14626 =
                 let uu____14627 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14636 =
                   let uu____14647 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14656 =
                     let uu____14667 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14667]  in
                   uu____14647 :: uu____14656  in
                 uu____14627 :: uu____14636  in
               cons1 uu____14626 t.FStar_Syntax_Syntax.pos) l uu____14590
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
        | uu____14739 -> false
=======
        | uu____14776 -> false
>>>>>>> snap
=======
        | uu____14776 -> false
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
          | uu____14853 -> false
=======
          | uu____14890 -> false
>>>>>>> snap
=======
          | uu____14890 -> false
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
        | uu____15019 -> false
=======
        | uu____15056 -> false
>>>>>>> snap
=======
        | uu____15056 -> false
>>>>>>> snap
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
<<<<<<< HEAD
<<<<<<< HEAD
        ((let uu____15057 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15057
=======
        ((let uu____15094 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15094
>>>>>>> snap
=======
        ((let uu____15094 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15094
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
        let t11 = let uu____15270 = unmeta_safe t1  in canon_app uu____15270
           in
        let t21 = let uu____15276 = unmeta_safe t2  in canon_app uu____15276
           in
        let uu____15279 =
          let uu____15284 =
            let uu____15285 =
              let uu____15288 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15288  in
            uu____15285.FStar_Syntax_Syntax.n  in
          let uu____15289 =
            let uu____15290 =
              let uu____15293 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15293  in
            uu____15290.FStar_Syntax_Syntax.n  in
          (uu____15284, uu____15289)  in
        match uu____15279 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15295,uu____15296) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15305,FStar_Syntax_Syntax.Tm_uinst uu____15306) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15315,uu____15316) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15341,FStar_Syntax_Syntax.Tm_delayed uu____15342) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15367,uu____15368) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15397,FStar_Syntax_Syntax.Tm_ascribed uu____15398) ->
=======
        let t11 = let uu____15316 = unmeta_safe t1  in canon_app uu____15316
           in
        let t21 = let uu____15322 = unmeta_safe t2  in canon_app uu____15322
           in
        let uu____15325 =
          let uu____15330 =
            let uu____15331 =
              let uu____15334 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15334  in
            uu____15331.FStar_Syntax_Syntax.n  in
          let uu____15335 =
            let uu____15336 =
              let uu____15339 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15339  in
            uu____15336.FStar_Syntax_Syntax.n  in
          (uu____15330, uu____15335)  in
        match uu____15325 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15341,uu____15342) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15351,FStar_Syntax_Syntax.Tm_uinst uu____15352) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15361,uu____15362) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15387,FStar_Syntax_Syntax.Tm_delayed uu____15388) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15413,uu____15414) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15443,FStar_Syntax_Syntax.Tm_ascribed uu____15444) ->
>>>>>>> snap
=======
        let t11 = let uu____15316 = unmeta_safe t1  in canon_app uu____15316
           in
        let t21 = let uu____15322 = unmeta_safe t2  in canon_app uu____15322
           in
        let uu____15325 =
          let uu____15330 =
            let uu____15331 =
              let uu____15334 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15334  in
            uu____15331.FStar_Syntax_Syntax.n  in
          let uu____15335 =
            let uu____15336 =
              let uu____15339 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15339  in
            uu____15336.FStar_Syntax_Syntax.n  in
          (uu____15330, uu____15335)  in
        match uu____15325 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15341,uu____15342) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15351,FStar_Syntax_Syntax.Tm_uinst uu____15352) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15361,uu____15362) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15387,FStar_Syntax_Syntax.Tm_delayed uu____15388) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15413,uu____15414) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15443,FStar_Syntax_Syntax.Tm_ascribed uu____15444) ->
>>>>>>> snap
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
<<<<<<< HEAD
<<<<<<< HEAD
            let uu____15437 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15437
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15442 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15442
        | (FStar_Syntax_Syntax.Tm_type
           uu____15445,FStar_Syntax_Syntax.Tm_type uu____15446) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15504 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15504) &&
              (let uu____15514 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15514)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15563 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15563) &&
              (let uu____15573 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15573)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15590 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15590) &&
              (let uu____15594 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15594)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15651 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15651) &&
              (let uu____15655 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15655)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15744 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15744) &&
              (let uu____15748 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15748)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15765,uu____15766) ->
            let uu____15767 =
              let uu____15769 = unlazy t11  in
              term_eq_dbg dbg uu____15769 t21  in
            check "lazy_l" uu____15767
        | (uu____15771,FStar_Syntax_Syntax.Tm_lazy uu____15772) ->
            let uu____15773 =
              let uu____15775 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15775  in
            check "lazy_r" uu____15773
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15820 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15820))
              &&
              (let uu____15824 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15824)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15828),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15830)) ->
=======
            let uu____15483 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15483
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15488 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15488
        | (FStar_Syntax_Syntax.Tm_type
           uu____15491,FStar_Syntax_Syntax.Tm_type uu____15492) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15550 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15550) &&
              (let uu____15560 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15560)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15609 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15609) &&
              (let uu____15619 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15619)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15636 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15636) &&
              (let uu____15640 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15640)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15697 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15697) &&
              (let uu____15701 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15701)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15790 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15790) &&
              (let uu____15794 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15794)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15811,uu____15812) ->
            let uu____15813 =
              let uu____15815 = unlazy t11  in
              term_eq_dbg dbg uu____15815 t21  in
            check "lazy_l" uu____15813
        | (uu____15817,FStar_Syntax_Syntax.Tm_lazy uu____15818) ->
            let uu____15819 =
              let uu____15821 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15821  in
            check "lazy_r" uu____15819
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15866 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15866))
              &&
              (let uu____15870 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15870)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15874),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15876)) ->
>>>>>>> snap
=======
            let uu____15483 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15483
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15488 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15488
        | (FStar_Syntax_Syntax.Tm_type
           uu____15491,FStar_Syntax_Syntax.Tm_type uu____15492) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15550 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15550) &&
              (let uu____15560 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15560)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15609 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15609) &&
              (let uu____15619 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15619)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15636 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15636) &&
              (let uu____15640 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15640)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15697 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15697) &&
              (let uu____15701 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15701)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15790 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15790) &&
              (let uu____15794 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15794)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15811,uu____15812) ->
            let uu____15813 =
              let uu____15815 = unlazy t11  in
              term_eq_dbg dbg uu____15815 t21  in
            check "lazy_l" uu____15813
        | (uu____15817,FStar_Syntax_Syntax.Tm_lazy uu____15818) ->
            let uu____15819 =
              let uu____15821 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15821  in
            check "lazy_r" uu____15819
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15866 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15866))
              &&
              (let uu____15870 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15870)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15874),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15876)) ->
>>>>>>> snap
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
<<<<<<< HEAD
<<<<<<< HEAD
            (let uu____15888 =
               let uu____15890 = eq_quoteinfo qi1 qi2  in uu____15890 = Equal
                in
             check "tm_quoted qi" uu____15888) &&
              (let uu____15893 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15893)
=======
=======
>>>>>>> snap
            (let uu____15934 =
               let uu____15936 = eq_quoteinfo qi1 qi2  in uu____15936 = Equal
                in
             check "tm_quoted qi" uu____15934) &&
              (let uu____15939 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15939)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
<<<<<<< HEAD
<<<<<<< HEAD
                 (let uu____15923 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15923) &&
                   (let uu____15927 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15927)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15946 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15946) &&
                    (let uu____15950 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15950))
                   &&
                   (let uu____15954 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15954)
             | uu____15957 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15963) -> fail "unk"
        | (uu____15965,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15967,uu____15968) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15970,uu____15971) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15973,uu____15974) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15976,uu____15977) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15979,uu____15980) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15982,uu____15983) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____16003,uu____16004) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____16020,uu____16021) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____16029,uu____16030) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____16048,uu____16049) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16073,uu____16074) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16089,uu____16090) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16104,uu____16105) ->
            fail "bottom"
        | (uu____16113,FStar_Syntax_Syntax.Tm_bvar uu____16114) ->
            fail "bottom"
        | (uu____16116,FStar_Syntax_Syntax.Tm_name uu____16117) ->
            fail "bottom"
        | (uu____16119,FStar_Syntax_Syntax.Tm_fvar uu____16120) ->
            fail "bottom"
        | (uu____16122,FStar_Syntax_Syntax.Tm_constant uu____16123) ->
            fail "bottom"
        | (uu____16125,FStar_Syntax_Syntax.Tm_type uu____16126) ->
            fail "bottom"
        | (uu____16128,FStar_Syntax_Syntax.Tm_abs uu____16129) ->
            fail "bottom"
        | (uu____16149,FStar_Syntax_Syntax.Tm_arrow uu____16150) ->
            fail "bottom"
        | (uu____16166,FStar_Syntax_Syntax.Tm_refine uu____16167) ->
            fail "bottom"
        | (uu____16175,FStar_Syntax_Syntax.Tm_app uu____16176) ->
            fail "bottom"
        | (uu____16194,FStar_Syntax_Syntax.Tm_match uu____16195) ->
            fail "bottom"
        | (uu____16219,FStar_Syntax_Syntax.Tm_let uu____16220) ->
            fail "bottom"
        | (uu____16235,FStar_Syntax_Syntax.Tm_uvar uu____16236) ->
            fail "bottom"
        | (uu____16250,FStar_Syntax_Syntax.Tm_meta uu____16251) ->
=======
                 (let uu____15969 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15969) &&
                   (let uu____15973 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15973)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15992 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15992) &&
                    (let uu____15996 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15996))
                   &&
                   (let uu____16000 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____16000)
             | uu____16003 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____16009) -> fail "unk"
        | (uu____16011,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____16013,uu____16014) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____16016,uu____16017) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____16019,uu____16020) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____16022,uu____16023) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____16025,uu____16026) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____16028,uu____16029) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____16049,uu____16050) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____16066,uu____16067) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____16075,uu____16076) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____16094,uu____16095) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16119,uu____16120) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16135,uu____16136) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16150,uu____16151) ->
            fail "bottom"
        | (uu____16159,FStar_Syntax_Syntax.Tm_bvar uu____16160) ->
            fail "bottom"
        | (uu____16162,FStar_Syntax_Syntax.Tm_name uu____16163) ->
            fail "bottom"
        | (uu____16165,FStar_Syntax_Syntax.Tm_fvar uu____16166) ->
            fail "bottom"
        | (uu____16168,FStar_Syntax_Syntax.Tm_constant uu____16169) ->
            fail "bottom"
        | (uu____16171,FStar_Syntax_Syntax.Tm_type uu____16172) ->
            fail "bottom"
        | (uu____16174,FStar_Syntax_Syntax.Tm_abs uu____16175) ->
            fail "bottom"
        | (uu____16195,FStar_Syntax_Syntax.Tm_arrow uu____16196) ->
            fail "bottom"
        | (uu____16212,FStar_Syntax_Syntax.Tm_refine uu____16213) ->
            fail "bottom"
        | (uu____16221,FStar_Syntax_Syntax.Tm_app uu____16222) ->
            fail "bottom"
        | (uu____16240,FStar_Syntax_Syntax.Tm_match uu____16241) ->
            fail "bottom"
        | (uu____16265,FStar_Syntax_Syntax.Tm_let uu____16266) ->
            fail "bottom"
        | (uu____16281,FStar_Syntax_Syntax.Tm_uvar uu____16282) ->
            fail "bottom"
        | (uu____16296,FStar_Syntax_Syntax.Tm_meta uu____16297) ->
>>>>>>> snap
=======
                 (let uu____15969 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15969) &&
                   (let uu____15973 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15973)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15992 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15992) &&
                    (let uu____15996 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15996))
                   &&
                   (let uu____16000 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____16000)
             | uu____16003 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____16009) -> fail "unk"
        | (uu____16011,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____16013,uu____16014) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____16016,uu____16017) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____16019,uu____16020) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____16022,uu____16023) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____16025,uu____16026) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____16028,uu____16029) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____16049,uu____16050) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____16066,uu____16067) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____16075,uu____16076) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____16094,uu____16095) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16119,uu____16120) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16135,uu____16136) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16150,uu____16151) ->
            fail "bottom"
        | (uu____16159,FStar_Syntax_Syntax.Tm_bvar uu____16160) ->
            fail "bottom"
        | (uu____16162,FStar_Syntax_Syntax.Tm_name uu____16163) ->
            fail "bottom"
        | (uu____16165,FStar_Syntax_Syntax.Tm_fvar uu____16166) ->
            fail "bottom"
        | (uu____16168,FStar_Syntax_Syntax.Tm_constant uu____16169) ->
            fail "bottom"
        | (uu____16171,FStar_Syntax_Syntax.Tm_type uu____16172) ->
            fail "bottom"
        | (uu____16174,FStar_Syntax_Syntax.Tm_abs uu____16175) ->
            fail "bottom"
        | (uu____16195,FStar_Syntax_Syntax.Tm_arrow uu____16196) ->
            fail "bottom"
        | (uu____16212,FStar_Syntax_Syntax.Tm_refine uu____16213) ->
            fail "bottom"
        | (uu____16221,FStar_Syntax_Syntax.Tm_app uu____16222) ->
            fail "bottom"
        | (uu____16240,FStar_Syntax_Syntax.Tm_match uu____16241) ->
            fail "bottom"
        | (uu____16265,FStar_Syntax_Syntax.Tm_let uu____16266) ->
            fail "bottom"
        | (uu____16281,FStar_Syntax_Syntax.Tm_uvar uu____16282) ->
            fail "bottom"
        | (uu____16296,FStar_Syntax_Syntax.Tm_meta uu____16297) ->
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
               let uu____16286 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16286)
          (fun q1  ->
             fun q2  ->
               let uu____16298 =
                 let uu____16300 = eq_aqual q1 q2  in uu____16300 = Equal  in
               check "arg qual" uu____16298) a1 a2
=======
               let uu____16332 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16332)
          (fun q1  ->
             fun q2  ->
               let uu____16344 =
                 let uu____16346 = eq_aqual q1 q2  in uu____16346 = Equal  in
               check "arg qual" uu____16344) a1 a2
>>>>>>> snap
=======
               let uu____16332 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16332)
          (fun q1  ->
             fun q2  ->
               let uu____16344 =
                 let uu____16346 = eq_aqual q1 q2  in uu____16346 = Equal  in
               check "arg qual" uu____16344) a1 a2
>>>>>>> snap

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
<<<<<<< HEAD
<<<<<<< HEAD
               let uu____16325 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16325)
          (fun q1  ->
             fun q2  ->
               let uu____16337 =
                 let uu____16339 = eq_aqual q1 q2  in uu____16339 = Equal  in
               check "binder qual" uu____16337) b1 b2
=======
               let uu____16371 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16371)
          (fun q1  ->
             fun q2  ->
=======
               let uu____16371 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16371)
          (fun q1  ->
             fun q2  ->
>>>>>>> snap
               let uu____16383 =
                 let uu____16385 = eq_aqual q1 q2  in uu____16385 = Equal  in
               check "binder qual" uu____16383) b1 b2

and (lcomp_eq_dbg :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c1  -> fun c2  -> fail "lcomp"
>>>>>>> snap

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
<<<<<<< HEAD
<<<<<<< HEAD
        ((let uu____16356 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16356) &&
           (let uu____16360 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16360))
=======
        ((let uu____16405 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16405) &&
           (let uu____16409 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16409))
>>>>>>> snap
=======
        ((let uu____16405 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16405) &&
           (let uu____16409 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16409))
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
    fun uu____16370  ->
      fun uu____16371  ->
        match (uu____16370, uu____16371) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16498 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16498) &&
               (let uu____16502 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16502))
              &&
              (let uu____16506 =
=======
    fun uu____16419  ->
      fun uu____16420  ->
        match (uu____16419, uu____16420) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16547 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16547) &&
               (let uu____16551 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16551))
              &&
              (let uu____16555 =
>>>>>>> snap
=======
    fun uu____16419  ->
      fun uu____16420  ->
        match (uu____16419, uu____16420) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16547 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16547) &&
               (let uu____16551 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16551))
              &&
              (let uu____16555 =
>>>>>>> snap
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
<<<<<<< HEAD
<<<<<<< HEAD
                 | uu____16548 -> false  in
               check "branch when" uu____16506)
=======
                 | uu____16597 -> false  in
               check "branch when" uu____16555)
>>>>>>> snap
=======
                 | uu____16597 -> false  in
               check "branch when" uu____16555)
>>>>>>> snap

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
<<<<<<< HEAD
<<<<<<< HEAD
        ((let uu____16569 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16569) &&
           (let uu____16578 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16578))
          &&
          (let uu____16582 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16582)
=======
=======
>>>>>>> snap
        ((let uu____16618 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16618) &&
           (let uu____16627 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16627))
          &&
          (let uu____16631 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16631)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____16599 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16599 t1 t2  in
=======
        let uu____16648 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16648 t1 t2  in
>>>>>>> snap
=======
        let uu____16648 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16648 t1 t2  in
>>>>>>> snap
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_delayed uu____16653 ->
        let uu____16676 =
          let uu____16678 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16678  in
        Prims.int_one + uu____16676
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16681 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16681
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16685 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16685
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16694 = sizeof t1  in (FStar_List.length us) + uu____16694
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16698) ->
        let uu____16723 = sizeof t1  in
        let uu____16725 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16740  ->
                 match uu____16740 with
                 | (bv,uu____16750) ->
                     let uu____16755 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16755) Prims.int_zero bs
           in
        uu____16723 + uu____16725
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____16784 = sizeof hd1  in
        let uu____16786 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16801  ->
                 match uu____16801 with
                 | (arg,uu____16811) ->
                     let uu____16816 = sizeof arg  in acc + uu____16816)
            Prims.int_zero args
           in
        uu____16784 + uu____16786
    | uu____16819 -> Prims.int_one
=======
=======
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_delayed uu____16702 ->
        let uu____16725 =
          let uu____16727 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16727  in
        Prims.int_one + uu____16725
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16730 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16730
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16734 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16734
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16743 = sizeof t1  in (FStar_List.length us) + uu____16743
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16747) ->
        let uu____16772 = sizeof t1  in
        let uu____16774 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16789  ->
                 match uu____16789 with
                 | (bv,uu____16799) ->
                     let uu____16804 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16804) Prims.int_zero bs
           in
        uu____16772 + uu____16774
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____16833 = sizeof hd1  in
        let uu____16835 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16850  ->
                 match uu____16850 with
                 | (arg,uu____16860) ->
                     let uu____16865 = sizeof arg  in acc + uu____16865)
            Prims.int_zero args
           in
        uu____16833 + uu____16835
    | uu____16868 -> Prims.int_one
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____16833 =
        let uu____16834 = un_uinst t  in uu____16834.FStar_Syntax_Syntax.n
         in
      match uu____16833 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16839 -> false
=======
      let uu____16882 =
        let uu____16883 = un_uinst t  in uu____16883.FStar_Syntax_Syntax.n
         in
      match uu____16882 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16888 -> false
>>>>>>> snap
=======
      let uu____16882 =
        let uu____16883 = un_uinst t  in uu____16883.FStar_Syntax_Syntax.n
         in
      match uu____16882 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16888 -> false
>>>>>>> snap
  
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
           let uu____16949 = head_and_args t  in
           match uu____16949 with
           | (head1,args) ->
               let uu____17004 =
                 let uu____17005 = FStar_Syntax_Subst.compress head1  in
                 uu____17005.FStar_Syntax_Syntax.n  in
               (match uu____17004 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____17031 -> FStar_Pervasives_Native.None)) attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options1 s =
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____16883 = FStar_Options.set_options s  in
        match uu____16883 with
=======
        let uu____17061 = FStar_Options.set_options s  in
        match uu____17061 with
>>>>>>> snap
=======
        let uu____17061 = FStar_Options.set_options s  in
        match uu____17061 with
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
          ((let uu____16897 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16897 (fun a1  -> ()));
=======
          ((let uu____17075 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____17075 (fun a1  -> ()));
>>>>>>> snap
=======
          ((let uu____17075 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____17075 (fun a1  -> ()));
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____16912 = FStar_Options.internal_pop ()  in
          if uu____16912
=======
          let uu____17090 = FStar_Options.internal_pop ()  in
          if uu____17090
>>>>>>> snap
=======
          let uu____17090 = FStar_Options.internal_pop ()  in
          if uu____17090
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_delayed uu____16944 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____16971 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____16986 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____16987 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____16988 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16997) ->
        let uu____17022 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17022 with
         | (bs1,t2) ->
             let uu____17031 =
               FStar_List.collect
                 (fun uu____17043  ->
                    match uu____17043 with
                    | (b,uu____17053) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17058 = unbound_variables t2  in
             FStar_List.append uu____17031 uu____17058)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17083 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17083 with
         | (bs1,c1) ->
             let uu____17092 =
               FStar_List.collect
                 (fun uu____17104  ->
                    match uu____17104 with
                    | (b,uu____17114) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17119 = unbound_variables_comp c1  in
             FStar_List.append uu____17092 uu____17119)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17128 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17128 with
         | (bs,t2) ->
             let uu____17151 =
               FStar_List.collect
                 (fun uu____17163  ->
                    match uu____17163 with
                    | (b1,uu____17173) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17178 = unbound_variables t2  in
             FStar_List.append uu____17151 uu____17178)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17207 =
          FStar_List.collect
            (fun uu____17221  ->
               match uu____17221 with
               | (x,uu____17233) -> unbound_variables x) args
           in
        let uu____17242 = unbound_variables t1  in
        FStar_List.append uu____17207 uu____17242
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17283 = unbound_variables t1  in
        let uu____17286 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17301 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17301 with
                  | (p,wopt,t2) ->
                      let uu____17323 = unbound_variables t2  in
                      let uu____17326 =
=======
=======
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_delayed uu____17122 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17149 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17164 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17165 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17166 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17175) ->
        let uu____17200 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17200 with
         | (bs1,t2) ->
             let uu____17209 =
               FStar_List.collect
                 (fun uu____17221  ->
                    match uu____17221 with
                    | (b,uu____17231) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17236 = unbound_variables t2  in
             FStar_List.append uu____17209 uu____17236)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17261 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17261 with
         | (bs1,c1) ->
             let uu____17270 =
               FStar_List.collect
                 (fun uu____17282  ->
                    match uu____17282 with
                    | (b,uu____17292) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17297 = unbound_variables_comp c1  in
             FStar_List.append uu____17270 uu____17297)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17306 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17306 with
         | (bs,t2) ->
             let uu____17329 =
               FStar_List.collect
                 (fun uu____17341  ->
                    match uu____17341 with
                    | (b1,uu____17351) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17356 = unbound_variables t2  in
             FStar_List.append uu____17329 uu____17356)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17385 =
          FStar_List.collect
            (fun uu____17399  ->
               match uu____17399 with
               | (x,uu____17411) -> unbound_variables x) args
           in
        let uu____17420 = unbound_variables t1  in
        FStar_List.append uu____17385 uu____17420
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17461 = unbound_variables t1  in
        let uu____17464 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17479 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17479 with
                  | (p,wopt,t2) ->
                      let uu____17501 = unbound_variables t2  in
                      let uu____17504 =
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
<<<<<<< HEAD
<<<<<<< HEAD
                      FStar_List.append uu____17323 uu____17326))
           in
        FStar_List.append uu____17283 uu____17286
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17340) ->
        let uu____17381 = unbound_variables t1  in
        let uu____17384 =
          let uu____17387 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17418 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17387 uu____17418  in
        FStar_List.append uu____17381 uu____17384
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17459 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17462 =
          let uu____17465 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17468 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17473 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17475 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17475 with
                 | (uu____17496,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17465 uu____17468  in
        FStar_List.append uu____17459 uu____17462
    | FStar_Syntax_Syntax.Tm_let ((uu____17498,lbs),t1) ->
        let uu____17518 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17518 with
         | (lbs1,t2) ->
             let uu____17533 = unbound_variables t2  in
             let uu____17536 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17543 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17546 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17543 uu____17546) lbs1
                in
             FStar_List.append uu____17533 uu____17536)
=======
                      FStar_List.append uu____17501 uu____17504))
           in
        FStar_List.append uu____17461 uu____17464
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17518) ->
        let uu____17559 = unbound_variables t1  in
        let uu____17562 =
          let uu____17565 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17596 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17565 uu____17596  in
        FStar_List.append uu____17559 uu____17562
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17637 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17640 =
          let uu____17643 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17646 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17651 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17653 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17653 with
                 | (uu____17674,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17643 uu____17646  in
        FStar_List.append uu____17637 uu____17640
    | FStar_Syntax_Syntax.Tm_let ((uu____17676,lbs),t1) ->
        let uu____17696 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17696 with
         | (lbs1,t2) ->
             let uu____17711 = unbound_variables t2  in
             let uu____17714 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17721 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17724 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17721 uu____17724) lbs1
                in
             FStar_List.append uu____17711 uu____17714)
>>>>>>> snap
=======
                      FStar_List.append uu____17501 uu____17504))
           in
        FStar_List.append uu____17461 uu____17464
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17518) ->
        let uu____17559 = unbound_variables t1  in
        let uu____17562 =
          let uu____17565 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17596 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17565 uu____17596  in
        FStar_List.append uu____17559 uu____17562
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17637 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17640 =
          let uu____17643 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17646 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17651 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17653 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17653 with
                 | (uu____17674,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17643 uu____17646  in
        FStar_List.append uu____17637 uu____17640
    | FStar_Syntax_Syntax.Tm_let ((uu____17676,lbs),t1) ->
        let uu____17696 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17696 with
         | (lbs1,t2) ->
             let uu____17711 = unbound_variables t2  in
             let uu____17714 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17721 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17724 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17721 uu____17724) lbs1
                in
             FStar_List.append uu____17711 uu____17714)
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____17563 = unbound_variables t1  in
        let uu____17566 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17571,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17626  ->
                      match uu____17626 with
                      | (a,uu____17638) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17647,uu____17648,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17654,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17660 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17669 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17670 -> []  in
        FStar_List.append uu____17563 uu____17566
=======
=======
>>>>>>> snap
        let uu____17741 = unbound_variables t1  in
        let uu____17744 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17749,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17804  ->
                      match uu____17804 with
                      | (a,uu____17816) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17825,uu____17826,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17832,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17838 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17847 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17848 -> []  in
        FStar_List.append uu____17741 uu____17744
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_Syntax_Syntax.GTotal (t,uu____17677) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17687) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17697 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17700 =
          FStar_List.collect
            (fun uu____17714  ->
               match uu____17714 with
               | (a,uu____17726) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17697 uu____17700
=======
    | FStar_Syntax_Syntax.GTotal (t,uu____17855) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17865) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17875 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17878 =
          FStar_List.collect
            (fun uu____17892  ->
               match uu____17892 with
               | (a,uu____17904) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17875 uu____17878
>>>>>>> snap
=======
    | FStar_Syntax_Syntax.GTotal (t,uu____17855) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17865) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17875 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17878 =
          FStar_List.collect
            (fun uu____17892  ->
               match uu____17892 with
               | (a,uu____17904) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17875 uu____17878
>>>>>>> snap

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
<<<<<<< HEAD
<<<<<<< HEAD
            let uu____17841 = head_and_args h  in
            (match uu____17841 with
             | (head1,args) ->
                 let uu____17902 =
                   let uu____17903 = FStar_Syntax_Subst.compress head1  in
                   uu____17903.FStar_Syntax_Syntax.n  in
                 (match uu____17902 with
=======
=======
>>>>>>> snap
            let uu____18019 = head_and_args h  in
            (match uu____18019 with
             | (head1,args) ->
                 let uu____18080 =
                   let uu____18081 = FStar_Syntax_Subst.compress head1  in
                   uu____18081.FStar_Syntax_Syntax.n  in
                 (match uu____18080 with
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
<<<<<<< HEAD
<<<<<<< HEAD
                  | uu____17956 -> aux (h :: acc) t))
=======
                  | uu____18134 -> aux (h :: acc) t))
>>>>>>> snap
=======
                  | uu____18134 -> aux (h :: acc) t))
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____17980 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____17980 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2483_18022 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2483_18022.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2483_18022.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2483_18022.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2483_18022.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
=======
      let uu____18158 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18158 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2531_18200 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2531_18200.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2531_18200.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2531_18200.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
=======
      let uu____18158 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18158 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2531_18200 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2531_18200.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2531_18200.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2531_18200.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
>>>>>>> snap
                  (uu___2531_18200.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2531_18200.FStar_Syntax_Syntax.sigopts)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____18030 =
      let uu____18031 = FStar_Syntax_Subst.compress t  in
      uu____18031.FStar_Syntax_Syntax.n  in
    match uu____18030 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18035,c) ->
=======
=======
>>>>>>> snap
    let uu____18208 =
      let uu____18209 = FStar_Syntax_Subst.compress t  in
      uu____18209.FStar_Syntax_Syntax.n  in
    match uu____18208 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18213,c) ->
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
<<<<<<< HEAD
<<<<<<< HEAD
              | _req::_ens::(pats,uu____18063)::uu____18064 ->
                  let pats' = unmeta pats  in
                  let uu____18124 = head_and_args pats'  in
                  (match uu____18124 with
                   | (head1,uu____18143) ->
                       let uu____18168 =
                         let uu____18169 = un_uinst head1  in
                         uu____18169.FStar_Syntax_Syntax.n  in
                       (match uu____18168 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18174 -> false))
              | uu____18176 -> false)
         | uu____18188 -> false)
    | uu____18190 -> false
=======
              | _req::_ens::(pats,uu____18241)::uu____18242 ->
                  let pats' = unmeta pats  in
                  let uu____18302 = head_and_args pats'  in
                  (match uu____18302 with
                   | (head1,uu____18321) ->
                       let uu____18346 =
                         let uu____18347 = un_uinst head1  in
                         uu____18347.FStar_Syntax_Syntax.n  in
                       (match uu____18346 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
=======
              | _req::_ens::(pats,uu____18241)::uu____18242 ->
                  let pats' = unmeta pats  in
                  let uu____18302 = head_and_args pats'  in
                  (match uu____18302 with
                   | (head1,uu____18321) ->
                       let uu____18346 =
                         let uu____18347 = un_uinst head1  in
                         uu____18347.FStar_Syntax_Syntax.n  in
                       (match uu____18346 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
>>>>>>> snap
                        | uu____18352 -> false))
              | uu____18354 -> false)
         | uu____18366 -> false)
    | uu____18368 -> false
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____18206 =
      let uu____18223 = unmeta e  in head_and_args uu____18223  in
    match uu____18206 with
    | (head1,args) ->
        let uu____18254 =
          let uu____18269 =
            let uu____18270 = un_uinst head1  in
            uu____18270.FStar_Syntax_Syntax.n  in
          (uu____18269, args)  in
        (match uu____18254 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18288) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18312::(hd1,uu____18314)::(tl1,uu____18316)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18383 =
               let uu____18386 =
                 let uu____18389 = list_elements tl1  in
                 FStar_Util.must uu____18389  in
               hd1 :: uu____18386  in
             FStar_Pervasives_Native.Some uu____18383
         | uu____18398 -> FStar_Pervasives_Native.None)
=======
=======
>>>>>>> snap
    let uu____18384 =
      let uu____18401 = unmeta e  in head_and_args uu____18401  in
    match uu____18384 with
    | (head1,args) ->
        let uu____18432 =
          let uu____18447 =
            let uu____18448 = un_uinst head1  in
            uu____18448.FStar_Syntax_Syntax.n  in
          (uu____18447, args)  in
        (match uu____18432 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18466) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18490::(hd1,uu____18492)::(tl1,uu____18494)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18561 =
               let uu____18564 =
                 let uu____18567 = list_elements tl1  in
                 FStar_Util.must uu____18567  in
               hd1 :: uu____18564  in
             FStar_Pervasives_Native.Some uu____18561
         | uu____18576 -> FStar_Pervasives_Native.None)
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____18427 =
      let uu____18428 = FStar_Syntax_Subst.compress t  in
      uu____18428.FStar_Syntax_Syntax.n  in
    match uu____18427 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18435) ->
        let uu____18470 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18470 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18504 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18504
             then
               let uu____18511 =
                 let uu____18522 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18522]  in
               mk_app t uu____18511
             else e1)
    | uu____18549 ->
        let uu____18550 =
          let uu____18561 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18561]  in
        mk_app t uu____18550
=======
=======
>>>>>>> snap
    let uu____18605 =
      let uu____18606 = FStar_Syntax_Subst.compress t  in
      uu____18606.FStar_Syntax_Syntax.n  in
    match uu____18605 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18613) ->
        let uu____18648 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18648 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18682 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18682
             then
               let uu____18689 =
                 let uu____18700 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18700]  in
               mk_app t uu____18689
             else e1)
    | uu____18727 ->
        let uu____18728 =
          let uu____18739 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18739]  in
        mk_app t uu____18728
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____18616 = list_elements e  in
        match uu____18616 with
=======
        let uu____18794 = list_elements e  in
        match uu____18794 with
>>>>>>> snap
=======
        let uu____18794 = list_elements e  in
        match uu____18794 with
>>>>>>> snap
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____18647 =
          let uu____18664 = unmeta p  in
          FStar_All.pipe_right uu____18664 head_and_args  in
        match uu____18647 with
        | (head1,args) ->
            let uu____18715 =
              let uu____18730 =
                let uu____18731 = un_uinst head1  in
                uu____18731.FStar_Syntax_Syntax.n  in
              (uu____18730, args)  in
            (match uu____18715 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18753,uu____18754)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18806 -> failwith "Unexpected pattern term")
=======
        let uu____18825 =
          let uu____18842 = unmeta p  in
          FStar_All.pipe_right uu____18842 head_and_args  in
        match uu____18825 with
        | (head1,args) ->
            let uu____18893 =
              let uu____18908 =
                let uu____18909 = un_uinst head1  in
                uu____18909.FStar_Syntax_Syntax.n  in
              (uu____18908, args)  in
            (match uu____18893 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18931,uu____18932)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18984 -> failwith "Unexpected pattern term")
>>>>>>> snap
=======
        let uu____18825 =
          let uu____18842 = unmeta p  in
          FStar_All.pipe_right uu____18842 head_and_args  in
        match uu____18825 with
        | (head1,args) ->
            let uu____18893 =
              let uu____18908 =
                let uu____18909 = un_uinst head1  in
                uu____18909.FStar_Syntax_Syntax.n  in
              (uu____18908, args)  in
            (match uu____18893 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18931,uu____18932)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18984 -> failwith "Unexpected pattern term")
>>>>>>> snap
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____18861 =
            let uu____18878 = unmeta t1  in
            FStar_All.pipe_right uu____18878 head_and_args  in
          match uu____18861 with
          | (head1,args) ->
              let uu____18925 =
                let uu____18940 =
                  let uu____18941 = un_uinst head1  in
                  uu____18941.FStar_Syntax_Syntax.n  in
                (uu____18940, args)  in
              (match uu____18925 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____18960)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____18997 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19027 = smt_pat_or1 t1  in
            (match uu____19027 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19049 = list_elements1 e  in
                 FStar_All.pipe_right uu____19049
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19079 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19079
                           (FStar_List.map one_pat)))
             | uu____19102 ->
                 let uu____19107 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19107])
        | uu____19158 ->
            let uu____19161 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19161]
         in
      let uu____19212 =
        let uu____19245 =
          let uu____19246 = FStar_Syntax_Subst.compress t  in
          uu____19246.FStar_Syntax_Syntax.n  in
        match uu____19245 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19303 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19303 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19374;
                        FStar_Syntax_Syntax.effect_name = uu____19375;
                        FStar_Syntax_Syntax.result_typ = uu____19376;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19378)::(post,uu____19380)::(pats,uu____19382)::[];
                        FStar_Syntax_Syntax.flags = uu____19383;_}
                      ->
                      let uu____19444 = lemma_pats pats  in
                      (binders1, pre, post, uu____19444)
                  | uu____19481 -> failwith "impos"))
        | uu____19515 -> failwith "Impos"  in
      match uu____19212 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19607 =
              let uu____19614 =
                let uu____19615 =
                  let uu____19622 = mk_imp pre post1  in
                  let uu____19625 =
                    let uu____19626 =
                      let uu____19647 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19647, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19626  in
                  (uu____19622, uu____19625)  in
                FStar_Syntax_Syntax.Tm_meta uu____19615  in
              FStar_Syntax_Syntax.mk uu____19614  in
            uu____19607 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19671 = universe_of_binders binders  in
=======
=======
>>>>>>> snap
          let uu____19039 =
            let uu____19056 = unmeta t1  in
            FStar_All.pipe_right uu____19056 head_and_args  in
          match uu____19039 with
          | (head1,args) ->
              let uu____19103 =
                let uu____19118 =
                  let uu____19119 = un_uinst head1  in
                  uu____19119.FStar_Syntax_Syntax.n  in
                (uu____19118, args)  in
              (match uu____19103 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19138)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19175 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19205 = smt_pat_or1 t1  in
            (match uu____19205 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19227 = list_elements1 e  in
                 FStar_All.pipe_right uu____19227
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19257 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19257
                           (FStar_List.map one_pat)))
             | uu____19280 ->
                 let uu____19285 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19285])
        | uu____19336 ->
            let uu____19339 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19339]
         in
      let uu____19390 =
        let uu____19423 =
          let uu____19424 = FStar_Syntax_Subst.compress t  in
          uu____19424.FStar_Syntax_Syntax.n  in
        match uu____19423 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19481 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19481 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19552;
                        FStar_Syntax_Syntax.effect_name = uu____19553;
                        FStar_Syntax_Syntax.result_typ = uu____19554;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19556)::(post,uu____19558)::(pats,uu____19560)::[];
                        FStar_Syntax_Syntax.flags = uu____19561;_}
                      ->
                      let uu____19622 = lemma_pats pats  in
                      (binders1, pre, post, uu____19622)
                  | uu____19659 -> failwith "impos"))
        | uu____19693 -> failwith "Impos"  in
      match uu____19390 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19785 =
              let uu____19792 =
                let uu____19793 =
                  let uu____19800 = mk_imp pre post1  in
                  let uu____19803 =
                    let uu____19804 =
                      let uu____19825 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19825, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19804  in
                  (uu____19800, uu____19803)  in
                FStar_Syntax_Syntax.Tm_meta uu____19793  in
              FStar_Syntax_Syntax.mk uu____19792  in
            uu____19785 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19849 = universe_of_binders binders  in
<<<<<<< HEAD
>>>>>>> snap
=======
>>>>>>> snap
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
<<<<<<< HEAD
<<<<<<< HEAD
              uu____19671 body
=======
              uu____19849 body
>>>>>>> snap
=======
              uu____19849 body
>>>>>>> snap
             in
          quant
  