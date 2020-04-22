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
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____85 =
      let uu____86 = FStar_Ident.ns_of_lid lid  in
      let uu____89 =
        let uu____92 =
          let uu____93 =
            let uu____99 =
              let uu____101 =
                let uu____103 =
                  let uu____105 = FStar_Ident.ident_of_lid lid  in
                  FStar_Ident.text_of_id uu____105  in
                Prims.op_Hat "is_" uu____103  in
              Prims.op_Hat FStar_Ident.reserved_prefix uu____101  in
            let uu____107 = FStar_Ident.range_of_lid lid  in
            (uu____99, uu____107)  in
          FStar_Ident.mk_ident uu____93  in
        [uu____92]  in
      FStar_List.append uu____86 uu____89  in
    FStar_Ident.lid_of_ids uu____85
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      let uu____118 =
        let uu____120 = FStar_Ident.ident_of_lid lid  in
        FStar_Ident.text_of_id uu____120  in
      FStar_Util.char_at uu____118 Prims.int_zero  in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'uuuuuu127 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu127) ->
      (FStar_Syntax_Syntax.term * 'uuuuuu127)
  =
  fun uu____140  ->
    match uu____140 with
    | (b,imp) ->
        let uu____147 = FStar_Syntax_Syntax.bv_to_name b  in (uu____147, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____199 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____199
            then []
            else (let uu____218 = arg_of_non_null_binder b  in [uu____218])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____253 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____335 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____335
              then
                let b1 =
                  let uu____361 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____361, (FStar_Pervasives_Native.snd b))  in
                let uu____368 = arg_of_non_null_binder b1  in (b1, uu____368)
              else
                (let uu____391 = arg_of_non_null_binder b  in (b, uu____391))))
       in
    FStar_All.pipe_right uu____253 FStar_List.unzip
  
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
              let uu____525 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____525
              then
                let uu____534 = b  in
                match uu____534 with
                | (a,imp) ->
                    let b1 =
                      let uu____554 =
                        let uu____556 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____556  in
                      FStar_Ident.id_of_text uu____554  in
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
        let uu____601 =
          let uu____608 =
            let uu____609 =
              let uu____624 = name_binders binders  in (uu____624, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____609  in
          FStar_Syntax_Syntax.mk uu____608  in
        uu____601 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____643 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____680  ->
            match uu____680 with
            | (t,imp) ->
                let uu____691 =
                  let uu____692 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____692
                   in
                (uu____691, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____747  ->
            match uu____747 with
            | (t,imp) ->
                let uu____764 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____764, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____777 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____777
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'uuuuuu789 . 'uuuuuu789 -> 'uuuuuu789 Prims.list =
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
          (fun uu____915  ->
             fun uu____916  ->
               match (uu____915, uu____916) with
               | ((x,uu____942),(y,uu____944)) ->
                   let uu____965 =
                     let uu____972 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____972)  in
                   FStar_Syntax_Syntax.NT uu____965) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____988) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____994,uu____995) -> unmeta e2
    | uu____1036 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____1050 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____1057 -> e1
         | uu____1066 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1068,uu____1069) ->
        unmeta_safe e2
    | uu____1110 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_name uu____1129 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_unif uu____1132 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_max uu____1145 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_zero  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1153 = univ_kernel u1  in
        (match uu____1153 with | (k,n) -> (k, (n + Prims.int_one)))
    | FStar_Syntax_Syntax.U_bvar uu____1170 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____1185 = univ_kernel u  in FStar_Pervasives_Native.snd uu____1185
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      let rec compare_kernel uk1 uk2 =
        match (uk1, uk2) with
        | (FStar_Syntax_Syntax.U_bvar uu____1218,uu____1219) ->
            failwith "Impossible: compare_kernel bvar"
        | (uu____1223,FStar_Syntax_Syntax.U_bvar uu____1224) ->
            failwith "Impossible: compare_kernel bvar"
        | (FStar_Syntax_Syntax.U_succ uu____1228,uu____1229) ->
            failwith "Impossible: compare_kernel succ"
        | (uu____1232,FStar_Syntax_Syntax.U_succ uu____1233) ->
            failwith "Impossible: compare_kernel succ"
        | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_unknown ,uu____1237) -> ~- Prims.int_one
        | (uu____1239,FStar_Syntax_Syntax.U_unknown ) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_zero ,uu____1242) -> ~- Prims.int_one
        | (uu____1244,FStar_Syntax_Syntax.U_zero ) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
            let uu____1248 = FStar_Ident.text_of_id u11  in
            let uu____1250 = FStar_Ident.text_of_id u21  in
            FStar_String.compare uu____1248 uu____1250
        | (FStar_Syntax_Syntax.U_name uu____1252,uu____1253) ->
            ~- Prims.int_one
        | (uu____1255,FStar_Syntax_Syntax.U_name uu____1256) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
            let uu____1280 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
            let uu____1282 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
            uu____1280 - uu____1282
        | (FStar_Syntax_Syntax.U_unif uu____1284,uu____1285) ->
            ~- Prims.int_one
        | (uu____1297,FStar_Syntax_Syntax.U_unif uu____1298) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
            let n1 = FStar_List.length us1  in
            let n2 = FStar_List.length us2  in
            if n1 <> n2
            then n1 - n2
            else
              (let copt =
                 let uu____1326 = FStar_List.zip us1 us2  in
                 FStar_Util.find_map uu____1326
                   (fun uu____1342  ->
                      match uu____1342 with
                      | (u11,u21) ->
                          let c = compare_univs u11 u21  in
                          if c <> Prims.int_zero
                          then FStar_Pervasives_Native.Some c
                          else FStar_Pervasives_Native.None)
                  in
               match copt with
               | FStar_Pervasives_Native.None  -> Prims.int_zero
               | FStar_Pervasives_Native.Some c -> c)
         in
      let uu____1370 = univ_kernel u1  in
      match uu____1370 with
      | (uk1,n1) ->
          let uu____1381 = univ_kernel u2  in
          (match uu____1381 with
           | (uk2,n2) ->
               let uu____1392 = compare_kernel uk1 uk2  in
               (match uu____1392 with
                | uu____1395 when uu____1395 = Prims.int_zero -> n1 - n2
                | n -> n))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1410 = compare_univs u1 u2  in uu____1410 = Prims.int_zero
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1429 =
        let uu____1430 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1430;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1429
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1450 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1459 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1482 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1491 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1518 =
          let uu____1519 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1519  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1518;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1548 =
          let uu____1549 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1549  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1548;
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
      let uu___231_1585 = c  in
      let uu____1586 =
        let uu____1587 =
          let uu___233_1588 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___233_1588.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___233_1588.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___233_1588.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___233_1588.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1587  in
      {
        FStar_Syntax_Syntax.n = uu____1586;
        FStar_Syntax_Syntax.pos = (uu___231_1585.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___231_1585.FStar_Syntax_Syntax.vars)
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
    | uu____1628 ->
        failwith "Assertion failed: Computation type without universe"
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1650)::[] -> wp
      | uu____1675 ->
          let uu____1686 =
            let uu____1688 =
              FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name  in
            let uu____1690 =
              let uu____1692 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length
                 in
              FStar_All.pipe_right uu____1692 FStar_Util.string_of_int  in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args"
              uu____1688 uu____1690
             in
          failwith uu____1686
       in
    let uu____1716 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1716, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1730 -> true
    | FStar_Syntax_Syntax.GTotal uu____1740 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1765  ->
               match uu___0_1765 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1769 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1786  ->
            match uu___1_1786 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1790 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1822 -> true
    | FStar_Syntax_Syntax.GTotal uu____1832 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_1847  ->
                   match uu___2_1847 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1850 -> false)))
  
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
    let uu____1891 =
      let uu____1892 = FStar_Syntax_Subst.compress t  in
      uu____1892.FStar_Syntax_Syntax.n  in
    match uu____1891 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1896,c) -> is_pure_or_ghost_comp c
    | uu____1918 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1933 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1942 =
      let uu____1943 = FStar_Syntax_Subst.compress t  in
      uu____1943.FStar_Syntax_Syntax.n  in
    match uu____1942 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1947,c) -> is_lemma_comp c
    | uu____1969 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1977 =
      let uu____1978 = FStar_Syntax_Subst.compress t  in
      uu____1978.FStar_Syntax_Syntax.n  in
    match uu____1977 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1982) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____2008) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2045,t1,uu____2047) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2073,uu____2074) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2116) -> head_of t1
    | uu____2121 -> t
  
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
    | FStar_Syntax_Syntax.Tm_app (head,args) -> (head, args)
    | uu____2199 -> (t1, [])
  
let rec (head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head,args) ->
        let uu____2281 = head_and_args' head  in
        (match uu____2281 with
         | (head1,args') -> (head1, (FStar_List.append args' args)))
    | uu____2350 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2377) ->
        FStar_Syntax_Subst.compress t2
    | uu____2382 -> t1
  
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
                (fun uu___3_2400  ->
                   match uu___3_2400 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2403 -> false)))
    | uu____2405 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2422) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2432) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2461 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2470 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___372_2482 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___372_2482.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___372_2482.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___372_2482.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___372_2482.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2498  ->
            match uu___4_2498 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2502 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2510 -> []
    | FStar_Syntax_Syntax.GTotal uu____2527 -> []
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
    | uu____2571 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2581,uu____2582) ->
        unascribe e2
    | uu____2623 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2676,uu____2677) ->
          ascribe t' k
      | uu____2718 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2745 =
      let uu____2754 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2754  in
    uu____2745 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2810 =
      let uu____2811 = FStar_Syntax_Subst.compress t  in
      uu____2811.FStar_Syntax_Syntax.n  in
    match uu____2810 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2815 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2815
    | uu____2816 -> t
  
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2823 =
      let uu____2824 = FStar_Syntax_Subst.compress t  in
      uu____2824.FStar_Syntax_Syntax.n  in
    match uu____2823 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2828 ->
             let uu____2837 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____2837
         | uu____2838 -> t)
    | uu____2839 -> t
  
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
      | uu____2864 -> false
  
let unlazy_as_t :
  'uuuuuu2877 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'uuuuuu2877
  =
  fun k  ->
    fun t  ->
      let uu____2888 =
        let uu____2889 = FStar_Syntax_Subst.compress t  in
        uu____2889.FStar_Syntax_Syntax.n  in
      match uu____2888 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2894;
            FStar_Syntax_Syntax.rng = uu____2895;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____2898 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2939 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2939;
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
    let uu____2952 =
      let uu____2967 = unascribe t  in head_and_args' uu____2967  in
    match uu____2952 with
    | (hd,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____3001 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____3012 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____3023 -> false
  
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
      | (NotEqual ,uu____3073) -> NotEqual
      | (uu____3074,NotEqual ) -> NotEqual
      | (Unknown ,uu____3075) -> Unknown
      | (uu____3076,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___5_3185 = if uu___5_3185 then Equal else Unknown  in
      let equal_iff uu___6_3196 = if uu___6_3196 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____3217 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3239 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3239
        then
          let uu____3243 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3320  ->
                    match uu____3320 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3361 = eq_tm a1 a2  in
                        eq_inj acc uu____3361) Equal) uu____3243
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3375 =
          let uu____3392 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3392 head_and_args  in
        match uu____3375 with
        | (head1,args1) ->
            let uu____3445 =
              let uu____3462 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3462 head_and_args  in
            (match uu____3445 with
             | (head2,args2) ->
                 let uu____3515 =
                   let uu____3520 =
                     let uu____3521 = un_uinst head1  in
                     uu____3521.FStar_Syntax_Syntax.n  in
                   let uu____3524 =
                     let uu____3525 = un_uinst head2  in
                     uu____3525.FStar_Syntax_Syntax.n  in
                   (uu____3520, uu____3524)  in
                 (match uu____3515 with
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
                  | uu____3552 -> FStar_Pervasives_Native.None))
         in
      let t12 = unmeta t11  in
      let t22 = unmeta t21  in
      match ((t12.FStar_Syntax_Syntax.n), (t22.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3570,uu____3571) ->
          let uu____3572 = unlazy t12  in eq_tm uu____3572 t22
      | (uu____3573,FStar_Syntax_Syntax.Tm_lazy uu____3574) ->
          let uu____3575 = unlazy t22  in eq_tm t12 uu____3575
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          let uu____3578 = FStar_Syntax_Syntax.bv_eq a b  in
          equal_if uu____3578
      | uu____3580 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3604 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3604
            (fun uu____3652  ->
               match uu____3652 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3667 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3667
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3681 = eq_tm f g  in
          eq_and uu____3681
            (fun uu____3684  ->
               let uu____3685 = eq_univs_list us vs  in equal_if uu____3685)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3687),uu____3688) -> Unknown
      | (uu____3689,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3690)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3693 = FStar_Const.eq_const c d  in equal_iff uu____3693
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3696)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3698))) ->
          let uu____3727 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3727
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3781 =
            let uu____3786 =
              let uu____3787 = un_uinst h1  in
              uu____3787.FStar_Syntax_Syntax.n  in
            let uu____3790 =
              let uu____3791 = un_uinst h2  in
              uu____3791.FStar_Syntax_Syntax.n  in
            (uu____3786, uu____3790)  in
          (match uu____3781 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3797 =
                    let uu____3799 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3799  in
                  FStar_List.mem uu____3797 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3801 ->
               let uu____3806 = eq_tm h1 h2  in
               eq_and uu____3806 (fun uu____3808  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t13,bs1),FStar_Syntax_Syntax.Tm_match
         (t23,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3914 = FStar_List.zip bs1 bs2  in
            let uu____3977 = eq_tm t13 t23  in
            FStar_List.fold_right
              (fun uu____4014  ->
                 fun a  ->
                   match uu____4014 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4107  -> branch_matches b1 b2))
              uu____3914 uu____3977
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v) ->
          let uu____4112 = eq_univs u v  in equal_if uu____4112
      | (FStar_Syntax_Syntax.Tm_quoted (t13,q1),FStar_Syntax_Syntax.Tm_quoted
         (t23,q2)) ->
          let uu____4126 = eq_quoteinfo q1 q2  in
          eq_and uu____4126 (fun uu____4128  -> eq_tm t13 t23)
      | (FStar_Syntax_Syntax.Tm_refine
         (t13,phi1),FStar_Syntax_Syntax.Tm_refine (t23,phi2)) ->
          let uu____4141 =
            eq_tm t13.FStar_Syntax_Syntax.sort t23.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4141 (fun uu____4143  -> eq_tm phi1 phi2)
      | uu____4144 -> Unknown

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
      | ([],uu____4216) -> NotEqual
      | (uu____4247,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          let uu____4336 =
            let uu____4338 = FStar_Syntax_Syntax.bv_eq x1 x2  in
            Prims.op_Negation uu____4338  in
          if uu____4336
          then NotEqual
          else
            (let uu____4343 = eq_tm t1 t2  in
             match uu____4343 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4344 = eq_antiquotes a11 a21  in
                 (match uu____4344 with
                  | NotEqual  -> NotEqual
                  | uu____4345 -> Unknown)
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
        | (uu____4429,uu____4430) -> false  in
      let uu____4440 = b1  in
      match uu____4440 with
      | (p1,w1,t1) ->
          let uu____4474 = b2  in
          (match uu____4474 with
           | (p2,w2,t2) ->
               let uu____4508 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4508
               then
                 let uu____4511 =
                   (let uu____4515 = eq_tm t1 t2  in uu____4515 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4524 = eq_tm t11 t21  in
                             uu____4524 = Equal) w1 w2)
                    in
                 (if uu____4511 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4589)::a11,(b,uu____4592)::b1) ->
          let uu____4666 = eq_tm a b  in
          (match uu____4666 with
           | Equal  -> eq_args a11 b1
           | uu____4667 -> Unknown)
      | uu____4668 -> Unknown

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
      | (FStar_Pervasives_Native.None ,uu____4723) -> NotEqual
      | (uu____4730,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4760 -> NotEqual
  
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4777) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4783,uu____4784) ->
        unrefine t2
    | uu____4825 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4833 =
      let uu____4834 = FStar_Syntax_Subst.compress t  in
      uu____4834.FStar_Syntax_Syntax.n  in
    match uu____4833 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4838 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4853) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4858 ->
        let uu____4875 =
          let uu____4876 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4876 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4875 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4939,uu____4940) ->
        is_uvar t1
    | uu____4981 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4990 =
      let uu____4991 = unrefine t  in uu____4991.FStar_Syntax_Syntax.n  in
    match uu____4990 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head,uu____4997) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5023) -> is_unit t1
    | uu____5028 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5037 =
      let uu____5038 = FStar_Syntax_Subst.compress t  in
      uu____5038.FStar_Syntax_Syntax.n  in
    match uu____5037 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5043 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5052 =
      let uu____5053 = FStar_Syntax_Subst.compress e  in
      uu____5053.FStar_Syntax_Syntax.n  in
    match uu____5052 with
    | FStar_Syntax_Syntax.Tm_abs uu____5057 -> true
    | uu____5077 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5086 =
      let uu____5087 = FStar_Syntax_Subst.compress t  in
      uu____5087.FStar_Syntax_Syntax.n  in
    match uu____5086 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5091 -> true
    | uu____5107 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5117) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5123,uu____5124) ->
        pre_typ t2
    | uu____5165 -> t1
  
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
      let uu____5190 =
        let uu____5191 = un_uinst typ1  in uu____5191.FStar_Syntax_Syntax.n
         in
      match uu____5190 with
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let head1 = un_uinst head  in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5256 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5286 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5307,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5314) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5319,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5330,uu____5331,uu____5332,uu____5333,uu____5334) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5344,uu____5345,uu____5346,uu____5347) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5353,uu____5354,uu____5355,uu____5356,uu____5357) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5365,uu____5366) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5368,uu____5369) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5371 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5372 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5373 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5386 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5410 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5436  ->
    match uu___7_5436 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'uuuuuu5450 'uuuuuu5451 .
    ('uuuuuu5450 FStar_Syntax_Syntax.syntax * 'uuuuuu5451) ->
      FStar_Range.range
  =
  fun uu____5462  ->
    match uu____5462 with | (hd,uu____5470) -> hd.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'uuuuuu5484 'uuuuuu5485 .
    ('uuuuuu5484 FStar_Syntax_Syntax.syntax * 'uuuuuu5485) Prims.list ->
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
      | uu____5583 ->
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
      let uu____5642 =
        FStar_List.map
          (fun uu____5669  ->
             match uu____5669 with
             | (bv,aq) ->
                 let uu____5688 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5688, aq)) bs
         in
      mk_app f uu____5642
  
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
      let itext = FStar_Ident.text_of_id i  in
      let newi =
        if field_projector_contains_constructor itext
        then i
        else
          (let uu____5739 =
             let uu____5745 =
               let uu____5747 =
                 let uu____5749 = FStar_Ident.ident_of_lid lid  in
                 FStar_Ident.text_of_id uu____5749  in
               mk_field_projector_name_from_string uu____5747 itext  in
             let uu____5750 = FStar_Ident.range_of_id i  in
             (uu____5745, uu____5750)  in
           FStar_Ident.mk_ident uu____5739)
         in
      let uu____5752 =
        let uu____5753 = FStar_Ident.ns_of_lid lid  in
        FStar_List.append uu____5753 [newi]  in
      FStar_Ident.lid_of_ids uu____5752
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5775 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5775
          then
            let uu____5778 =
              let uu____5784 =
                let uu____5786 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5786  in
              let uu____5789 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5784, uu____5789)  in
            FStar_Ident.mk_ident uu____5778
          else x.FStar_Syntax_Syntax.ppname  in
        mk_field_projector_name_from_ident lid nm
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5804) -> ses
    | uu____5813 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5828 = FStar_Syntax_Unionfind.find uv  in
      match uu____5828 with
      | FStar_Pervasives_Native.Some uu____5831 ->
          let uu____5832 =
            let uu____5834 =
              let uu____5836 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5836  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5834  in
          failwith uu____5832
      | uu____5841 -> FStar_Syntax_Unionfind.change uv t
  
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
            (let uu____5865 = FStar_Ident.text_of_id l1b  in
             let uu____5867 = FStar_Ident.text_of_id l2b  in
             uu____5865 = uu____5867)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5896 = FStar_Ident.text_of_id x1  in
                      let uu____5898 = FStar_Ident.text_of_id x2  in
                      uu____5896 = uu____5898) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5907 = FStar_Ident.text_of_id x1  in
                    let uu____5909 = FStar_Ident.text_of_id x2  in
                    uu____5907 = uu____5909) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5938 = FStar_Ident.text_of_id x1  in
                      let uu____5940 = FStar_Ident.text_of_id x2  in
                      uu____5938 = uu____5940) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5949 = FStar_Ident.text_of_id x1  in
                    let uu____5951 = FStar_Ident.text_of_id x2  in
                    uu____5949 = uu____5951) f1 f2)
      | uu____5954 -> q1 = q2
  
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
              let uu____6000 =
                let uu___1000_6001 = rc  in
                let uu____6002 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1000_6001.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6002;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1000_6001.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6000
           in
        match bs with
        | [] -> t
        | uu____6019 ->
            let body =
              let uu____6021 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6021  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6051 =
                   let uu____6058 =
                     let uu____6059 =
                       let uu____6078 =
                         let uu____6087 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6087 bs'  in
                       let uu____6102 = close_lopt lopt'  in
                       (uu____6078, t1, uu____6102)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6059  in
                   FStar_Syntax_Syntax.mk uu____6058  in
                 uu____6051 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6117 ->
                 let uu____6118 =
                   let uu____6125 =
                     let uu____6126 =
                       let uu____6145 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6154 = close_lopt lopt  in
                       (uu____6145, body, uu____6154)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6126  in
                   FStar_Syntax_Syntax.mk uu____6125  in
                 uu____6118 FStar_Pervasives_Native.None
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
      | uu____6210 ->
          let uu____6219 =
            let uu____6226 =
              let uu____6227 =
                let uu____6242 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6251 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6242, uu____6251)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6227  in
            FStar_Syntax_Syntax.mk uu____6226  in
          uu____6219 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6300 =
        let uu____6301 = FStar_Syntax_Subst.compress t  in
        uu____6301.FStar_Syntax_Syntax.n  in
      match uu____6300 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6331) ->
               let uu____6340 =
                 let uu____6341 = FStar_Syntax_Subst.compress tres  in
                 uu____6341.FStar_Syntax_Syntax.n  in
               (match uu____6340 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6384 -> t)
           | uu____6385 -> t)
      | uu____6386 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6404 =
        let uu____6405 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6405 t.FStar_Syntax_Syntax.pos  in
      let uu____6406 =
        let uu____6413 =
          let uu____6414 =
            let uu____6421 =
              let uu____6424 =
                let uu____6425 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6425]  in
              FStar_Syntax_Subst.close uu____6424 t  in
            (b, uu____6421)  in
          FStar_Syntax_Syntax.Tm_refine uu____6414  in
        FStar_Syntax_Syntax.mk uu____6413  in
      uu____6406 FStar_Pervasives_Native.None uu____6404
  
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
        let uu____6505 = is_total_comp c  in
        if uu____6505
        then
          let uu____6520 = arrow_formals_comp_ln (comp_result c)  in
          (match uu____6520 with
           | (bs',k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6587;
           FStar_Syntax_Syntax.index = uu____6588;
           FStar_Syntax_Syntax.sort = s;_},uu____6590)
        ->
        let rec aux s1 k2 =
          let uu____6621 =
            let uu____6622 = FStar_Syntax_Subst.compress s1  in
            uu____6622.FStar_Syntax_Syntax.n  in
          match uu____6621 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6637 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6652;
                 FStar_Syntax_Syntax.index = uu____6653;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6655)
              -> aux s2 k2
          | uu____6663 ->
              let uu____6664 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6664)
           in
        aux s k1
    | uu____6679 ->
        let uu____6680 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6680)
  
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let uu____6705 = arrow_formals_comp_ln k  in
    match uu____6705 with | (bs,c) -> FStar_Syntax_Subst.open_comp bs c
  
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6760 = arrow_formals_comp_ln k  in
    match uu____6760 with | (bs,c) -> (bs, (comp_result c))
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6827 = arrow_formals_comp k  in
    match uu____6827 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6929 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6929 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6953 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_6962  ->
                         match uu___8_6962 with
                         | FStar_Syntax_Syntax.DECREASES uu____6964 -> true
                         | uu____6968 -> false))
                  in
               (match uu____6953 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7003 ->
                    let uu____7006 = is_total_comp c1  in
                    if uu____7006
                    then
                      let uu____7025 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7025 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7118;
             FStar_Syntax_Syntax.index = uu____7119;
             FStar_Syntax_Syntax.sort = k2;_},uu____7121)
          -> arrow_until_decreases k2
      | uu____7129 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7150 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7150 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7204 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7225 =
                 FStar_Common.tabulate n_univs (fun uu____7231  -> false)  in
               let uu____7234 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7259  ->
                         match uu____7259 with
                         | (x,uu____7268) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7225 uu____7234)
           in
        ((n_univs + (FStar_List.length bs)), uu____7204)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7324 =
            let uu___1127_7325 = rc  in
            let uu____7326 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1127_7325.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7326;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1127_7325.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7324
      | uu____7335 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7369 =
        let uu____7370 =
          let uu____7373 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7373  in
        uu____7370.FStar_Syntax_Syntax.n  in
      match uu____7369 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7419 = aux t2 what  in
          (match uu____7419 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7491 -> ([], t1, abs_body_lcomp)  in
    let uu____7508 = aux t FStar_Pervasives_Native.None  in
    match uu____7508 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7556 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7556 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let no_acc uu____7590 =
      match uu____7590 with
      | (b,aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true )) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7604 -> aq  in
          (b, aq1)
       in
    let uu____7609 = arrow_formals_comp_ln t  in
    match uu____7609 with
    | (bs,c) ->
        (match bs with
         | [] -> t
         | uu____7646 ->
             let uu____7655 =
               let uu____7662 =
                 let uu____7663 =
                   let uu____7678 = FStar_List.map no_acc bs  in
                   (uu____7678, c)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____7663  in
               FStar_Syntax_Syntax.mk uu____7662  in
             uu____7655 FStar_Pervasives_Native.None
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
                    | (FStar_Pervasives_Native.None ,uu____7849) -> def
                    | (uu____7860,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7872) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu____7888  ->
                                  FStar_Syntax_Syntax.U_name uu____7888))
                           in
                        let inst =
                          FStar_All.pipe_right fvs
                            (FStar_List.map
                               (fun fv  ->
                                  (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                    universes)))
                           in
                        FStar_Syntax_InstFV.instantiate inst def
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
            let uu____7970 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7970 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____8005 ->
            let t' = arrow binders c  in
            let uu____8017 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____8017 with
             | (uvs1,t'1) ->
                 let uu____8038 =
                   let uu____8039 = FStar_Syntax_Subst.compress t'1  in
                   uu____8039.FStar_Syntax_Syntax.n  in
                 (match uu____8038 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8088 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8113 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Parser_Const.is_tuple_constructor_string uu____8113
    | uu____8115 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8126 -> false
  
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
      let uu____8189 =
        let uu____8190 = pre_typ t  in uu____8190.FStar_Syntax_Syntax.n  in
      match uu____8189 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8195 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8209 =
        let uu____8210 = pre_typ t  in uu____8210.FStar_Syntax_Syntax.n  in
      match uu____8209 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8214 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8216) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8242) ->
          is_constructed_typ t1 lid
      | uu____8247 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8260 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8261 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8262 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8264) -> get_tycon t2
    | uu____8289 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8297 =
      let uu____8298 = un_uinst t  in uu____8298.FStar_Syntax_Syntax.n  in
    match uu____8297 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8303 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8317 =
        let uu____8321 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8321  in
      match uu____8317 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8353 -> false
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
  fun uu____8372  ->
    let u =
      let uu____8378 =
        FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
      FStar_All.pipe_left
        (fun uu____8399  -> FStar_Syntax_Syntax.U_unif uu____8399) uu____8378
       in
    let uu____8400 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8400, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8413 = eq_tm a a'  in
      match uu____8413 with | Equal  -> true | uu____8416 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8421 =
    let uu____8428 =
      let uu____8429 =
        let uu____8430 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8430
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8429  in
    FStar_Syntax_Syntax.mk uu____8428  in
  uu____8421 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8543 =
            let uu____8546 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8547 =
              let uu____8554 =
                let uu____8555 =
                  let uu____8572 =
                    let uu____8583 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8592 =
                      let uu____8603 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8603]  in
                    uu____8583 :: uu____8592  in
                  (tand, uu____8572)  in
                FStar_Syntax_Syntax.Tm_app uu____8555  in
              FStar_Syntax_Syntax.mk uu____8554  in
            uu____8547 FStar_Pervasives_Native.None uu____8546  in
          FStar_Pervasives_Native.Some uu____8543
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8680 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8681 =
          let uu____8688 =
            let uu____8689 =
              let uu____8706 =
                let uu____8717 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8726 =
                  let uu____8737 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8737]  in
                uu____8717 :: uu____8726  in
              (op_t, uu____8706)  in
            FStar_Syntax_Syntax.Tm_app uu____8689  in
          FStar_Syntax_Syntax.mk uu____8688  in
        uu____8681 FStar_Pervasives_Native.None uu____8680
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8794 =
      let uu____8801 =
        let uu____8802 =
          let uu____8819 =
            let uu____8830 = FStar_Syntax_Syntax.as_arg phi  in [uu____8830]
             in
          (t_not, uu____8819)  in
        FStar_Syntax_Syntax.Tm_app uu____8802  in
      FStar_Syntax_Syntax.mk uu____8801  in
    uu____8794 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    | hd::tl -> FStar_List.fold_right mk_conj tl hd
  
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
    | hd::tl -> FStar_List.fold_right mk_disj tl hd
  
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
    let uu____9027 =
      let uu____9034 =
        let uu____9035 =
          let uu____9052 =
            let uu____9063 = FStar_Syntax_Syntax.as_arg e  in [uu____9063]
             in
          (b2t_v, uu____9052)  in
        FStar_Syntax_Syntax.Tm_app uu____9035  in
      FStar_Syntax_Syntax.mk uu____9034  in
    uu____9027 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9110 = head_and_args e  in
    match uu____9110 with
    | (hd,args) ->
        let uu____9155 =
          let uu____9170 =
            let uu____9171 = FStar_Syntax_Subst.compress hd  in
            uu____9171.FStar_Syntax_Syntax.n  in
          (uu____9170, args)  in
        (match uu____9155 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9188)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9223 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9245 =
      let uu____9246 = unmeta t  in uu____9246.FStar_Syntax_Syntax.n  in
    match uu____9245 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9251 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9274 = is_t_true t1  in
      if uu____9274
      then t2
      else
        (let uu____9281 = is_t_true t2  in
         if uu____9281 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9309 = is_t_true t1  in
      if uu____9309
      then t_true
      else
        (let uu____9316 = is_t_true t2  in
         if uu____9316 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9345 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9346 =
        let uu____9353 =
          let uu____9354 =
            let uu____9371 =
              let uu____9382 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9391 =
                let uu____9402 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9402]  in
              uu____9382 :: uu____9391  in
            (teq, uu____9371)  in
          FStar_Syntax_Syntax.Tm_app uu____9354  in
        FStar_Syntax_Syntax.mk uu____9353  in
      uu____9346 FStar_Pervasives_Native.None uu____9345
  
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
          let uu____9469 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9470 =
            let uu____9477 =
              let uu____9478 =
                let uu____9495 =
                  let uu____9506 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9515 =
                    let uu____9526 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9535 =
                      let uu____9546 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9546]  in
                    uu____9526 :: uu____9535  in
                  uu____9506 :: uu____9515  in
                (eq_inst, uu____9495)  in
              FStar_Syntax_Syntax.Tm_app uu____9478  in
            FStar_Syntax_Syntax.mk uu____9477  in
          uu____9470 FStar_Pervasives_Native.None uu____9469
  
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
        let uu____9623 =
          let uu____9630 =
            let uu____9631 =
              let uu____9648 =
                let uu____9659 = FStar_Syntax_Syntax.iarg t  in
                let uu____9668 =
                  let uu____9679 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9688 =
                    let uu____9699 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9699]  in
                  uu____9679 :: uu____9688  in
                uu____9659 :: uu____9668  in
              (t_has_type1, uu____9648)  in
            FStar_Syntax_Syntax.Tm_app uu____9631  in
          FStar_Syntax_Syntax.mk uu____9630  in
        uu____9623 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9776 =
          let uu____9783 =
            let uu____9784 =
              let uu____9801 =
                let uu____9812 = FStar_Syntax_Syntax.iarg t  in
                let uu____9821 =
                  let uu____9832 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9832]  in
                uu____9812 :: uu____9821  in
              (t_with_type1, uu____9801)  in
            FStar_Syntax_Syntax.Tm_app uu____9784  in
          FStar_Syntax_Syntax.mk uu____9783  in
        uu____9776 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9879 =
    let uu____9886 =
      let uu____9887 =
        let uu____9894 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9894, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9887  in
    FStar_Syntax_Syntax.mk uu____9886  in
  uu____9879 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
        let uu____9977 =
          let uu____9984 =
            let uu____9985 =
              let uu____10002 =
                let uu____10013 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____10022 =
                  let uu____10033 =
                    let uu____10042 =
                      let uu____10043 =
                        let uu____10044 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10044]  in
                      abs uu____10043 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10042  in
                  [uu____10033]  in
                uu____10013 :: uu____10022  in
              (fa, uu____10002)  in
            FStar_Syntax_Syntax.Tm_app uu____9985  in
          FStar_Syntax_Syntax.mk uu____9984  in
        uu____9977 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10171 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10171
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10190 -> true
    | uu____10192 -> false
  
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
          let uu____10239 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10239, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10268 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10268, FStar_Pervasives_Native.None, t2)  in
        let uu____10282 =
          let uu____10283 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10283  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10282
  
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
      let uu____10359 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10362 =
        let uu____10373 = FStar_Syntax_Syntax.as_arg p  in [uu____10373]  in
      mk_app uu____10359 uu____10362
  
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
      let uu____10413 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10416 =
        let uu____10427 = FStar_Syntax_Syntax.as_arg p  in [uu____10427]  in
      mk_app uu____10413 uu____10416
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10462 = head_and_args t  in
    match uu____10462 with
    | (head,args) ->
        let head1 = unascribe head  in
        let head2 = un_uinst head1  in
        let uu____10511 =
          let uu____10526 =
            let uu____10527 = FStar_Syntax_Subst.compress head2  in
            uu____10527.FStar_Syntax_Syntax.n  in
          (uu____10526, args)  in
        (match uu____10511 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10546)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10612 =
                    let uu____10617 =
                      let uu____10618 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10618]  in
                    FStar_Syntax_Subst.open_term uu____10617 p  in
                  (match uu____10612 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10675 -> failwith "impossible"  in
                       let uu____10683 =
                         let uu____10685 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10685
                          in
                       if uu____10683
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10701 -> FStar_Pervasives_Native.None)
         | uu____10704 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10735 = head_and_args t  in
    match uu____10735 with
    | (head,args) ->
        let uu____10786 =
          let uu____10801 =
            let uu____10802 = FStar_Syntax_Subst.compress head  in
            uu____10802.FStar_Syntax_Syntax.n  in
          (uu____10801, args)  in
        (match uu____10786 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10824;
               FStar_Syntax_Syntax.vars = uu____10825;_},u::[]),(t1,uu____10828)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10875 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10910 = head_and_args t  in
    match uu____10910 with
    | (head,args) ->
        let uu____10961 =
          let uu____10976 =
            let uu____10977 = FStar_Syntax_Subst.compress head  in
            uu____10977.FStar_Syntax_Syntax.n  in
          (uu____10976, args)  in
        (match uu____10961 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10999;
               FStar_Syntax_Syntax.vars = uu____11000;_},u::[]),(t1,uu____11003)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11050 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11078 =
      let uu____11095 = unmeta t  in head_and_args uu____11095  in
    match uu____11078 with
    | (head,uu____11098) ->
        let uu____11123 =
          let uu____11124 = un_uinst head  in
          uu____11124.FStar_Syntax_Syntax.n  in
        (match uu____11123 with
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
         | uu____11129 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11149 =
      let uu____11150 = FStar_Syntax_Subst.compress t  in
      uu____11150.FStar_Syntax_Syntax.n  in
    match uu____11149 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11256 =
          let uu____11261 =
            let uu____11262 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11262  in
          (b, uu____11261)  in
        FStar_Pervasives_Native.Some uu____11256
    | uu____11267 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11290 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11290
      (fun uu____11318  ->
         match uu____11318 with
         | (b,c) ->
             let uu____11337 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11337 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11400 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11437 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11437
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11489 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11532 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11573 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11959) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11971) ->
          unmeta_monadic t
      | uu____11984 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12053 =
        match uu____12053 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12091  ->
                   match uu____12091 with
                   | (lid,out_lid) ->
                       let uu____12100 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12100
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12127 = head_and_args t  in
      match uu____12127 with
      | (hd,args) ->
          let uu____12172 =
            let uu____12173 = un_uinst hd  in
            uu____12173.FStar_Syntax_Syntax.n  in
          (match uu____12172 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12179 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12188 = un_squash t  in
      FStar_Util.bind_opt uu____12188
        (fun t1  ->
           let uu____12204 = head_and_args' t1  in
           match uu____12204 with
           | (hd,args) ->
               let uu____12243 =
                 let uu____12244 = un_uinst hd  in
                 uu____12244.FStar_Syntax_Syntax.n  in
               (match uu____12243 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12250 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12291,pats)) ->
          let uu____12329 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12329)
      | uu____12342 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12409 = head_and_args t1  in
        match uu____12409 with
        | (t2,args) ->
            let uu____12464 = un_uinst t2  in
            let uu____12465 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12506  ->
                      match uu____12506 with
                      | (t3,imp) ->
                          let uu____12525 = unascribe t3  in
                          (uu____12525, imp)))
               in
            (uu____12464, uu____12465)
         in
      let rec aux qopt out t1 =
        let uu____12576 = let uu____12600 = flat t1  in (qopt, uu____12600)
           in
        match uu____12576 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12640;
                 FStar_Syntax_Syntax.vars = uu____12641;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12644);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12645;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12646;_},uu____12647)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12749;
                 FStar_Syntax_Syntax.vars = uu____12750;_},uu____12751::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12754);
                  FStar_Syntax_Syntax.pos = uu____12755;
                  FStar_Syntax_Syntax.vars = uu____12756;_},uu____12757)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12874;
               FStar_Syntax_Syntax.vars = uu____12875;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12878);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12879;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12880;_},uu____12881)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12974 =
              let uu____12978 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12978  in
            aux uu____12974 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12988;
               FStar_Syntax_Syntax.vars = uu____12989;_},uu____12990::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12993);
                FStar_Syntax_Syntax.pos = uu____12994;
                FStar_Syntax_Syntax.vars = uu____12995;_},uu____12996)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13105 =
              let uu____13109 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13109  in
            aux uu____13105 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13119) ->
            let bs = FStar_List.rev out  in
            let uu____13172 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13172 with
             | (bs1,t2) ->
                 let uu____13181 = patterns t2  in
                 (match uu____13181 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13231 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13286 = un_squash t  in
      FStar_Util.bind_opt uu____13286
        (fun t1  ->
           let uu____13301 = arrow_one t1  in
           match uu____13301 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13316 =
                 let uu____13318 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13318  in
               if uu____13316
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13328 = comp_to_comp_typ_nouniv c  in
                    uu____13328.FStar_Syntax_Syntax.result_typ  in
                  let uu____13329 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13329
                  then
                    let uu____13336 = patterns q  in
                    match uu____13336 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13399 =
                       let uu____13400 =
                         let uu____13405 =
                           let uu____13406 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13417 =
                             let uu____13428 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13428]  in
                           uu____13406 :: uu____13417  in
                         (FStar_Parser_Const.imp_lid, uu____13405)  in
                       BaseConn uu____13400  in
                     FStar_Pervasives_Native.Some uu____13399))
           | uu____13461 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13469 = un_squash t  in
      FStar_Util.bind_opt uu____13469
        (fun t1  ->
           let uu____13500 = head_and_args' t1  in
           match uu____13500 with
           | (hd,args) ->
               let uu____13539 =
                 let uu____13554 =
                   let uu____13555 = un_uinst hd  in
                   uu____13555.FStar_Syntax_Syntax.n  in
                 (uu____13554, args)  in
               (match uu____13539 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13572)::(a2,uu____13574)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13625 =
                      let uu____13626 = FStar_Syntax_Subst.compress a2  in
                      uu____13626.FStar_Syntax_Syntax.n  in
                    (match uu____13625 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13633) ->
                         let uu____13668 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13668 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13721 -> failwith "impossible"  in
                              let uu____13729 = patterns q1  in
                              (match uu____13729 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13790 -> FStar_Pervasives_Native.None)
                | uu____13791 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13814 = destruct_sq_forall phi  in
          (match uu____13814 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13824  ->
                    FStar_Pervasives_Native.Some uu____13824)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13831 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13837 = destruct_sq_exists phi  in
          (match uu____13837 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13847  ->
                    FStar_Pervasives_Native.Some uu____13847)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13854 -> f1)
      | uu____13857 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13861 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13861
      (fun uu____13866  ->
         let uu____13867 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13867
           (fun uu____13872  ->
              let uu____13873 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13873
                (fun uu____13878  ->
                   let uu____13879 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13879
                     (fun uu____13884  ->
                        let uu____13885 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13885
                          (fun uu____13889  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13907 =
            let uu____13912 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13912  in
          let uu____13913 =
            let uu____13914 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13914  in
          let uu____13917 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13907 a.FStar_Syntax_Syntax.action_univs uu____13913
            FStar_Parser_Const.effect_Tot_lid uu____13917 [] pos
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
    let reify_ =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
       in
    let uu____13943 =
      let uu____13950 =
        let uu____13951 =
          let uu____13968 =
            let uu____13979 = FStar_Syntax_Syntax.as_arg t  in [uu____13979]
             in
          (reify_, uu____13968)  in
        FStar_Syntax_Syntax.Tm_app uu____13951  in
      FStar_Syntax_Syntax.mk uu____13950  in
    uu____13943 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14031 =
        let uu____14038 =
          let uu____14039 =
            let uu____14040 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14040  in
          FStar_Syntax_Syntax.Tm_constant uu____14039  in
        FStar_Syntax_Syntax.mk uu____14038  in
      uu____14031 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14042 =
      let uu____14049 =
        let uu____14050 =
          let uu____14067 =
            let uu____14078 = FStar_Syntax_Syntax.as_arg t  in [uu____14078]
             in
          (reflect_, uu____14067)  in
        FStar_Syntax_Syntax.Tm_app uu____14050  in
      FStar_Syntax_Syntax.mk uu____14049  in
    uu____14042 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14122 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14139 = unfold_lazy i  in delta_qualifier uu____14139
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14141 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14142 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14143 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14166 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14179 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14180 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14187 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14188 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14204) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14209;
           FStar_Syntax_Syntax.index = uu____14210;
           FStar_Syntax_Syntax.sort = t2;_},uu____14212)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14221) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14227,uu____14228) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14270) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14295,t2,uu____14297) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14322,t2) -> delta_qualifier t2
  
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
    let uu____14361 = delta_qualifier t  in incr_delta_depth uu____14361
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14369 =
      let uu____14370 = FStar_Syntax_Subst.compress t  in
      uu____14370.FStar_Syntax_Syntax.n  in
    match uu____14369 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14375 -> false
  
let rec apply_last :
  'uuuuuu14384 .
    ('uuuuuu14384 -> 'uuuuuu14384) ->
      'uuuuuu14384 Prims.list -> 'uuuuuu14384 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14410 = f a  in [uu____14410]
      | x::xs -> let uu____14415 = apply_last f xs  in x :: uu____14415
  
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
          let uu____14470 =
            let uu____14477 =
              let uu____14478 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14478  in
            FStar_Syntax_Syntax.mk uu____14477  in
          uu____14470 FStar_Pervasives_Native.None rng  in
        let cons args pos =
          let uu____14492 =
            let uu____14497 =
              let uu____14498 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14498
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14497 args  in
          uu____14492 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14512 =
            let uu____14517 =
              let uu____14518 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14518
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14517 args  in
          uu____14512 FStar_Pervasives_Native.None pos  in
        let uu____14519 =
          let uu____14520 =
            let uu____14521 = FStar_Syntax_Syntax.iarg typ  in [uu____14521]
             in
          nil uu____14520 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14555 =
                 let uu____14556 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14565 =
                   let uu____14576 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14585 =
                     let uu____14596 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14596]  in
                   uu____14576 :: uu____14585  in
                 uu____14556 :: uu____14565  in
               cons uu____14555 t.FStar_Syntax_Syntax.pos) l uu____14519
  
let rec eqlist :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq  ->
    fun xs  ->
      fun ys  ->
        match (xs, ys) with
        | ([],[]) -> true
        | (x::xs1,y::ys1) -> (eq x y) && (eqlist eq xs1 ys1)
        | uu____14705 -> false
  
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
          | uu____14819 -> false
  
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
        | uu____14985 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15023 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15023
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
        let t11 = let uu____15227 = unmeta_safe t1  in canon_app uu____15227
           in
        let t21 = let uu____15233 = unmeta_safe t2  in canon_app uu____15233
           in
        let uu____15236 =
          let uu____15241 =
            let uu____15242 =
              let uu____15245 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15245  in
            uu____15242.FStar_Syntax_Syntax.n  in
          let uu____15246 =
            let uu____15247 =
              let uu____15250 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15250  in
            uu____15247.FStar_Syntax_Syntax.n  in
          (uu____15241, uu____15246)  in
        match uu____15236 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15252,uu____15253) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15262,FStar_Syntax_Syntax.Tm_uinst uu____15263) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15272,uu____15273) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15290,FStar_Syntax_Syntax.Tm_delayed uu____15291) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15308,uu____15309) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15338,FStar_Syntax_Syntax.Tm_ascribed uu____15339) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15378 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15378
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15383 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15383
        | (FStar_Syntax_Syntax.Tm_type
           uu____15386,FStar_Syntax_Syntax.Tm_type uu____15387) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15445 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15445) &&
              (let uu____15455 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15455)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15504 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15504) &&
              (let uu____15514 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15514)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15531 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15531) &&
              (let uu____15535 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15535)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15592 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15592) &&
              (let uu____15596 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15596)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15685 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15685) &&
              (let uu____15689 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15689)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15706,uu____15707) ->
            let uu____15708 =
              let uu____15710 = unlazy t11  in
              term_eq_dbg dbg uu____15710 t21  in
            check "lazy_l" uu____15708
        | (uu____15712,FStar_Syntax_Syntax.Tm_lazy uu____15713) ->
            let uu____15714 =
              let uu____15716 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15716  in
            check "lazy_r" uu____15714
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15761 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15761))
              &&
              (let uu____15765 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15765)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15769),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15771)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15831 =
               let uu____15833 = eq_quoteinfo qi1 qi2  in uu____15833 = Equal
                in
             check "tm_quoted qi" uu____15831) &&
              (let uu____15836 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15836)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15866 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15866) &&
                   (let uu____15870 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15870)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15889 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15889) &&
                    (let uu____15893 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15893))
                   &&
                   (let uu____15897 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15897)
             | uu____15900 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15906) -> fail "unk"
        | (uu____15908,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15910,uu____15911) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15913,uu____15914) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15916,uu____15917) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15919,uu____15920) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15922,uu____15923) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15925,uu____15926) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15946,uu____15947) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15963,uu____15964) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15972,uu____15973) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15991,uu____15992) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16016,uu____16017) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16032,uu____16033) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16047,uu____16048) ->
            fail "bottom"
        | (uu____16056,FStar_Syntax_Syntax.Tm_bvar uu____16057) ->
            fail "bottom"
        | (uu____16059,FStar_Syntax_Syntax.Tm_name uu____16060) ->
            fail "bottom"
        | (uu____16062,FStar_Syntax_Syntax.Tm_fvar uu____16063) ->
            fail "bottom"
        | (uu____16065,FStar_Syntax_Syntax.Tm_constant uu____16066) ->
            fail "bottom"
        | (uu____16068,FStar_Syntax_Syntax.Tm_type uu____16069) ->
            fail "bottom"
        | (uu____16071,FStar_Syntax_Syntax.Tm_abs uu____16072) ->
            fail "bottom"
        | (uu____16092,FStar_Syntax_Syntax.Tm_arrow uu____16093) ->
            fail "bottom"
        | (uu____16109,FStar_Syntax_Syntax.Tm_refine uu____16110) ->
            fail "bottom"
        | (uu____16118,FStar_Syntax_Syntax.Tm_app uu____16119) ->
            fail "bottom"
        | (uu____16137,FStar_Syntax_Syntax.Tm_match uu____16138) ->
            fail "bottom"
        | (uu____16162,FStar_Syntax_Syntax.Tm_let uu____16163) ->
            fail "bottom"
        | (uu____16178,FStar_Syntax_Syntax.Tm_uvar uu____16179) ->
            fail "bottom"
        | (uu____16193,FStar_Syntax_Syntax.Tm_meta uu____16194) ->
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
               let uu____16229 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16229)
          (fun q1  ->
             fun q2  ->
               let uu____16241 =
                 let uu____16243 = eq_aqual q1 q2  in uu____16243 = Equal  in
               check "arg qual" uu____16241) a1 a2

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
               let uu____16268 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16268)
          (fun q1  ->
             fun q2  ->
               let uu____16280 =
                 let uu____16282 = eq_aqual q1 q2  in uu____16282 = Equal  in
               check "binder qual" uu____16280) b1 b2

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
        ((let uu____16296 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16296) &&
           (let uu____16300 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16300))
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
    fun uu____16310  ->
      fun uu____16311  ->
        match (uu____16310, uu____16311) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16438 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16438) &&
               (let uu____16442 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16442))
              &&
              (let uu____16446 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16488 -> false  in
               check "branch when" uu____16446)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16509 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16509) &&
           (let uu____16518 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16518))
          &&
          (let uu____16522 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16522)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16539 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16539 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16593 ->
        let uu____16608 =
          let uu____16610 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16610  in
        Prims.int_one + uu____16608
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16613 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16613
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16617 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16617
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16626 = sizeof t1  in (FStar_List.length us) + uu____16626
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16630) ->
        let uu____16655 = sizeof t1  in
        let uu____16657 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16672  ->
                 match uu____16672 with
                 | (bv,uu____16682) ->
                     let uu____16687 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16687) Prims.int_zero bs
           in
        uu____16655 + uu____16657
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____16716 = sizeof hd  in
        let uu____16718 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16733  ->
                 match uu____16733 with
                 | (arg,uu____16743) ->
                     let uu____16748 = sizeof arg  in acc + uu____16748)
            Prims.int_zero args
           in
        uu____16716 + uu____16718
    | uu____16751 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16765 =
        let uu____16766 = un_uinst t  in uu____16766.FStar_Syntax_Syntax.n
         in
      match uu____16765 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16771 -> false
  
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
           let uu____16832 = head_and_args t  in
           match uu____16832 with
           | (head,args) ->
               let uu____16887 =
                 let uu____16888 = FStar_Syntax_Subst.compress head  in
                 uu____16888.FStar_Syntax_Syntax.n  in
               (match uu____16887 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16914 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____16947 = is_fvar attr a  in Prims.op_Negation uu____16947)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      FStar_Errors.set_option_warning_callback_range
        (FStar_Pervasives_Native.Some r);
      (let set_options s =
         let uu____16969 = FStar_Options.set_options s  in
         match uu____16969 with
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
       | FStar_Syntax_Syntax.SetOptions o -> set_options o
       | FStar_Syntax_Syntax.ResetOptions sopt ->
           ((let uu____16983 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____16983 (fun uu____16985  -> ()));
            (match sopt with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some s -> set_options s))
       | FStar_Syntax_Syntax.PushOptions sopt ->
           (FStar_Options.internal_push ();
            (match sopt with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some s -> set_options s))
       | FStar_Syntax_Syntax.RestartSolver  -> ()
       | FStar_Syntax_Syntax.PopOptions  ->
           let uu____16999 = FStar_Options.internal_pop ()  in
           if uu____16999
           then ()
           else
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_FailToProcessPragma,
                 "Cannot #pop-options, stack would become empty") r)
  
let rec (unbound_variables :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun tm  ->
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____17031 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17050 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17065 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17066 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17067 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17076) ->
        let uu____17101 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17101 with
         | (bs1,t2) ->
             let uu____17110 =
               FStar_List.collect
                 (fun uu____17122  ->
                    match uu____17122 with
                    | (b,uu____17132) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17137 = unbound_variables t2  in
             FStar_List.append uu____17110 uu____17137)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17162 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17162 with
         | (bs1,c1) ->
             let uu____17171 =
               FStar_List.collect
                 (fun uu____17183  ->
                    match uu____17183 with
                    | (b,uu____17193) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17198 = unbound_variables_comp c1  in
             FStar_List.append uu____17171 uu____17198)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17207 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17207 with
         | (bs,t2) ->
             let uu____17230 =
               FStar_List.collect
                 (fun uu____17242  ->
                    match uu____17242 with
                    | (b1,uu____17252) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17257 = unbound_variables t2  in
             FStar_List.append uu____17230 uu____17257)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17286 =
          FStar_List.collect
            (fun uu____17300  ->
               match uu____17300 with
               | (x,uu____17312) -> unbound_variables x) args
           in
        let uu____17321 = unbound_variables t1  in
        FStar_List.append uu____17286 uu____17321
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17362 = unbound_variables t1  in
        let uu____17365 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17380 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17380 with
                  | (p,wopt,t2) ->
                      let uu____17402 = unbound_variables t2  in
                      let uu____17405 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17402 uu____17405))
           in
        FStar_List.append uu____17362 uu____17365
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17419) ->
        let uu____17460 = unbound_variables t1  in
        let uu____17463 =
          let uu____17466 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17497 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17466 uu____17497  in
        FStar_List.append uu____17460 uu____17463
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17538 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17541 =
          let uu____17544 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17547 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17552 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17554 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17554 with
                 | (uu____17575,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17544 uu____17547  in
        FStar_List.append uu____17538 uu____17541
    | FStar_Syntax_Syntax.Tm_let ((uu____17577,lbs),t1) ->
        let uu____17597 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17597 with
         | (lbs1,t2) ->
             let uu____17612 = unbound_variables t2  in
             let uu____17615 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17622 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17625 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17622 uu____17625) lbs1
                in
             FStar_List.append uu____17612 uu____17615)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17642 = unbound_variables t1  in
        let uu____17645 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17650,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17705  ->
                      match uu____17705 with
                      | (a,uu____17717) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17726,uu____17727,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17733,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17739 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17748 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17749 -> []  in
        FStar_List.append uu____17642 uu____17645

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17756) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17766) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17776 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17779 =
          FStar_List.collect
            (fun uu____17793  ->
               match uu____17793 with
               | (a,uu____17805) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17776 uu____17779

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
            let uu____17920 = head_and_args h  in
            (match uu____17920 with
             | (head,args) ->
                 let uu____17981 =
                   let uu____17982 = FStar_Syntax_Subst.compress head  in
                   uu____17982.FStar_Syntax_Syntax.n  in
                 (match uu____17981 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18035 -> aux (h :: acc) t))
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
      let uu____18059 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18059 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2483_18101 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2483_18101.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2483_18101.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2483_18101.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2483_18101.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2483_18101.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18109 =
      let uu____18110 = FStar_Syntax_Subst.compress t  in
      uu____18110.FStar_Syntax_Syntax.n  in
    match uu____18109 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18114,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18142)::uu____18143 ->
                  let pats' = unmeta pats  in
                  let uu____18203 = head_and_args pats'  in
                  (match uu____18203 with
                   | (head,uu____18222) ->
                       let uu____18247 =
                         let uu____18248 = un_uinst head  in
                         uu____18248.FStar_Syntax_Syntax.n  in
                       (match uu____18247 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18253 -> false))
              | uu____18255 -> false)
         | uu____18267 -> false)
    | uu____18269 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18285 =
      let uu____18302 = unmeta e  in head_and_args uu____18302  in
    match uu____18285 with
    | (head,args) ->
        let uu____18333 =
          let uu____18348 =
            let uu____18349 = un_uinst head  in
            uu____18349.FStar_Syntax_Syntax.n  in
          (uu____18348, args)  in
        (match uu____18333 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18367) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18391::(hd,uu____18393)::(tl,uu____18395)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18462 =
               let uu____18465 =
                 let uu____18468 = list_elements tl  in
                 FStar_Util.must uu____18468  in
               hd :: uu____18465  in
             FStar_Pervasives_Native.Some uu____18462
         | uu____18477 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18506 =
      let uu____18507 = FStar_Syntax_Subst.compress t  in
      uu____18507.FStar_Syntax_Syntax.n  in
    match uu____18506 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18514) ->
        let uu____18549 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18549 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18583 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18583
             then
               let uu____18590 =
                 let uu____18601 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18601]  in
               mk_app t uu____18590
             else e1)
    | uu____18628 ->
        let uu____18629 =
          let uu____18640 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18640]  in
        mk_app t uu____18629
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18695 = list_elements e  in
        match uu____18695 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18730 =
          let uu____18747 = unmeta p  in
          FStar_All.pipe_right uu____18747 head_and_args  in
        match uu____18730 with
        | (head,args) ->
            let uu____18798 =
              let uu____18813 =
                let uu____18814 = un_uinst head  in
                uu____18814.FStar_Syntax_Syntax.n  in
              (uu____18813, args)  in
            (match uu____18798 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18836,uu____18837)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18889 ->
                 let uu____18904 =
                   let uu____18910 =
                     let uu____18912 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18912
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____18910)  in
                 FStar_Errors.raise_error uu____18904
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____18955 =
            let uu____18972 = unmeta t1  in
            FStar_All.pipe_right uu____18972 head_and_args  in
          match uu____18955 with
          | (head,args) ->
              let uu____19019 =
                let uu____19034 =
                  let uu____19035 = un_uinst head  in
                  uu____19035.FStar_Syntax_Syntax.n  in
                (uu____19034, args)  in
              (match uu____19019 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19054)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19091 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19121 = smt_pat_or t1  in
            (match uu____19121 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19143 = list_elements1 e  in
                 FStar_All.pipe_right uu____19143
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19173 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19173
                           (FStar_List.map one_pat)))
             | uu____19202 ->
                 let uu____19207 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19207])
        | uu____19262 ->
            let uu____19265 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19265]
         in
      let uu____19320 =
        let uu____19353 =
          let uu____19354 = FStar_Syntax_Subst.compress t  in
          uu____19354.FStar_Syntax_Syntax.n  in
        match uu____19353 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19411 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19411 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19482;
                        FStar_Syntax_Syntax.effect_name = uu____19483;
                        FStar_Syntax_Syntax.result_typ = uu____19484;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19486)::(post,uu____19488)::(pats,uu____19490)::[];
                        FStar_Syntax_Syntax.flags = uu____19491;_}
                      ->
                      let uu____19552 = lemma_pats pats  in
                      (binders1, pre, post, uu____19552)
                  | uu____19589 -> failwith "impos"))
        | uu____19623 -> failwith "Impos"  in
      match uu____19320 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19715 =
              let uu____19722 =
                let uu____19723 =
                  let uu____19730 = mk_imp pre post1  in
                  let uu____19733 =
                    let uu____19734 =
                      let uu____19755 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19755, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19734  in
                  (uu____19730, uu____19733)  in
                FStar_Syntax_Syntax.Tm_meta uu____19723  in
              FStar_Syntax_Syntax.mk uu____19722  in
            uu____19715 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19779 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19779 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19809 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19820 -> true
    | uu____19822 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19833 -> true
    | uu____19835 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19853 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19854 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19855 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19856 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19857 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19858 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19859 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19860 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19863 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19866 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19853;
        FStar_Syntax_Syntax.bind_wp = uu____19854;
        FStar_Syntax_Syntax.stronger = uu____19855;
        FStar_Syntax_Syntax.if_then_else = uu____19856;
        FStar_Syntax_Syntax.ite_wp = uu____19857;
        FStar_Syntax_Syntax.close_wp = uu____19858;
        FStar_Syntax_Syntax.trivial = uu____19859;
        FStar_Syntax_Syntax.repr = uu____19860;
        FStar_Syntax_Syntax.return_repr = uu____19863;
        FStar_Syntax_Syntax.bind_repr = uu____19866
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____19898 =
        match uu____19898 with
        | (ts1,ts2) ->
            let uu____19909 = f ts1  in
            let uu____19910 = f ts2  in (uu____19909, uu____19910)
         in
      let uu____19911 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____19916 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____19921 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____19926 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____19931 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____19911;
        FStar_Syntax_Syntax.l_return = uu____19916;
        FStar_Syntax_Syntax.l_bind = uu____19921;
        FStar_Syntax_Syntax.l_subcomp = uu____19926;
        FStar_Syntax_Syntax.l_if_then_else = uu____19931
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
          let uu____19953 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____19953
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19955 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____19955
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19957 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____19957
  
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
    | uu____19972 -> FStar_Pervasives_Native.None
  
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
        let uu____19986 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19986
          (fun uu____19993  -> FStar_Pervasives_Native.Some uu____19993)
  
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
        let uu____20033 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20033
          (fun uu____20040  -> FStar_Pervasives_Native.Some uu____20040)
  
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
        let uu____20054 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20054
          (fun uu____20061  -> FStar_Pervasives_Native.Some uu____20061)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20075  -> FStar_Pervasives_Native.Some uu____20075)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20079  -> FStar_Pervasives_Native.Some uu____20079)
    | uu____20080 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20092 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20092
          (fun uu____20099  -> FStar_Pervasives_Native.Some uu____20099)
    | uu____20100 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20114  -> FStar_Pervasives_Native.Some uu____20114)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20118  -> FStar_Pervasives_Native.Some uu____20118)
    | uu____20119 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20133  -> FStar_Pervasives_Native.Some uu____20133)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20137  -> FStar_Pervasives_Native.Some uu____20137)
    | uu____20138 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20162 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20163 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20165 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20165
          (fun uu____20172  -> FStar_Pervasives_Native.Some uu____20172)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun uu____20186  -> FStar_Pervasives_Native.Some uu____20186)
    | uu____20187 -> FStar_Pervasives_Native.None
  