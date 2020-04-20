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
    | FStar_Syntax_Syntax.U_max uu____1143 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_zero  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1151 = univ_kernel u1  in
        (match uu____1151 with | (k,n) -> (k, (n + Prims.int_one)))
    | FStar_Syntax_Syntax.U_bvar uu____1168 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____1183 = univ_kernel u  in FStar_Pervasives_Native.snd uu____1183
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      let rec compare_kernel uk1 uk2 =
        match (uk1, uk2) with
        | (FStar_Syntax_Syntax.U_bvar uu____1216,uu____1217) ->
            failwith "Impossible: compare_kernel bvar"
        | (uu____1221,FStar_Syntax_Syntax.U_bvar uu____1222) ->
            failwith "Impossible: compare_kernel bvar"
        | (FStar_Syntax_Syntax.U_succ uu____1226,uu____1227) ->
            failwith "Impossible: compare_kernel succ"
        | (uu____1230,FStar_Syntax_Syntax.U_succ uu____1231) ->
            failwith "Impossible: compare_kernel succ"
        | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_unknown ,uu____1235) -> ~- Prims.int_one
        | (uu____1237,FStar_Syntax_Syntax.U_unknown ) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_zero ,uu____1240) -> ~- Prims.int_one
        | (uu____1242,FStar_Syntax_Syntax.U_zero ) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
            let uu____1246 = FStar_Ident.text_of_id u11  in
            let uu____1248 = FStar_Ident.text_of_id u21  in
            FStar_String.compare uu____1246 uu____1248
        | (FStar_Syntax_Syntax.U_name uu____1250,uu____1251) ->
            ~- Prims.int_one
        | (uu____1253,FStar_Syntax_Syntax.U_name uu____1254) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
            let uu____1274 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
            let uu____1276 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
            uu____1274 - uu____1276
        | (FStar_Syntax_Syntax.U_unif uu____1278,uu____1279) ->
            ~- Prims.int_one
        | (uu____1289,FStar_Syntax_Syntax.U_unif uu____1290) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
            let n1 = FStar_List.length us1  in
            let n2 = FStar_List.length us2  in
            if n1 <> n2
            then n1 - n2
            else
              (let copt =
                 let uu____1316 = FStar_List.zip us1 us2  in
                 FStar_Util.find_map uu____1316
                   (fun uu____1332  ->
                      match uu____1332 with
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
      let uu____1360 = univ_kernel u1  in
      match uu____1360 with
      | (uk1,n1) ->
          let uu____1371 = univ_kernel u2  in
          (match uu____1371 with
           | (uk2,n2) ->
               let uu____1382 = compare_kernel uk1 uk2  in
               (match uu____1382 with
                | uu____1385 when uu____1385 = Prims.int_zero -> n1 - n2
                | n -> n))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1400 = compare_univs u1 u2  in uu____1400 = Prims.int_zero
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1419 =
        let uu____1420 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1420;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1419
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1440 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1449 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1472 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1481 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1508 =
          let uu____1509 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1509  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1508;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1538 =
          let uu____1539 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1539  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1538;
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
      let uu___231_1575 = c  in
      let uu____1576 =
        let uu____1577 =
          let uu___233_1578 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___233_1578.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___233_1578.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___233_1578.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___233_1578.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1577  in
      {
        FStar_Syntax_Syntax.n = uu____1576;
        FStar_Syntax_Syntax.pos = (uu___231_1575.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___231_1575.FStar_Syntax_Syntax.vars)
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
    | uu____1618 ->
        failwith "Assertion failed: Computation type without universe"
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1640)::[] -> wp
      | uu____1665 ->
          let uu____1676 =
            let uu____1678 =
              FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name  in
            let uu____1680 =
              let uu____1682 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length
                 in
              FStar_All.pipe_right uu____1682 FStar_Util.string_of_int  in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args"
              uu____1678 uu____1680
             in
          failwith uu____1676
       in
    let uu____1706 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1706, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1720 -> true
    | FStar_Syntax_Syntax.GTotal uu____1730 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1755  ->
               match uu___0_1755 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1759 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1776  ->
            match uu___1_1776 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1780 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1812 -> true
    | FStar_Syntax_Syntax.GTotal uu____1822 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_1837  ->
                   match uu___2_1837 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1840 -> false)))
  
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
    let uu____1881 =
      let uu____1882 = FStar_Syntax_Subst.compress t  in
      uu____1882.FStar_Syntax_Syntax.n  in
    match uu____1881 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1886,c) -> is_pure_or_ghost_comp c
    | uu____1908 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1923 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1932 =
      let uu____1933 = FStar_Syntax_Subst.compress t  in
      uu____1933.FStar_Syntax_Syntax.n  in
    match uu____1932 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1937,c) -> is_lemma_comp c
    | uu____1959 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1967 =
      let uu____1968 = FStar_Syntax_Subst.compress t  in
      uu____1968.FStar_Syntax_Syntax.n  in
    match uu____1967 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1972) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____1998) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2035,t1,uu____2037) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2063,uu____2064) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2106) -> head_of t1
    | uu____2111 -> t
  
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
    | uu____2189 -> (t1, [])
  
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
        let uu____2271 = head_and_args' head  in
        (match uu____2271 with
         | (head1,args') -> (head1, (FStar_List.append args' args)))
    | uu____2340 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2367) ->
        FStar_Syntax_Subst.compress t2
    | uu____2372 -> t1
  
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
                (fun uu___3_2390  ->
                   match uu___3_2390 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2393 -> false)))
    | uu____2395 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2412) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2422) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2451 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2460 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___372_2472 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___372_2472.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___372_2472.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___372_2472.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___372_2472.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2488  ->
            match uu___4_2488 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2492 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2500 -> []
    | FStar_Syntax_Syntax.GTotal uu____2517 -> []
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
    | uu____2561 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2571,uu____2572) ->
        unascribe e2
    | uu____2613 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2666,uu____2667) ->
          ascribe t' k
      | uu____2708 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2735 =
      let uu____2744 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2744  in
    uu____2735 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2800 =
      let uu____2801 = FStar_Syntax_Subst.compress t  in
      uu____2801.FStar_Syntax_Syntax.n  in
    match uu____2800 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2805 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2805
    | uu____2806 -> t
  
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2813 =
      let uu____2814 = FStar_Syntax_Subst.compress t  in
      uu____2814.FStar_Syntax_Syntax.n  in
    match uu____2813 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2818 ->
             let uu____2827 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____2827
         | uu____2828 -> t)
    | uu____2829 -> t
  
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
      | uu____2854 -> false
  
let unlazy_as_t :
  'uuuuuu2867 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'uuuuuu2867
  =
  fun k  ->
    fun t  ->
      let uu____2878 =
        let uu____2879 = FStar_Syntax_Subst.compress t  in
        uu____2879.FStar_Syntax_Syntax.n  in
      match uu____2878 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2884;
            FStar_Syntax_Syntax.rng = uu____2885;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____2888 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2929 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2929;
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
    let uu____2942 =
      let uu____2957 = unascribe t  in head_and_args' uu____2957  in
    match uu____2942 with
    | (hd,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2991 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____3002 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____3013 -> false
  
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
      | (NotEqual ,uu____3063) -> NotEqual
      | (uu____3064,NotEqual ) -> NotEqual
      | (Unknown ,uu____3065) -> Unknown
      | (uu____3066,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___5_3175 = if uu___5_3175 then Equal else Unknown  in
      let equal_iff uu___6_3186 = if uu___6_3186 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____3207 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3229 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3229
        then
          let uu____3233 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3310  ->
                    match uu____3310 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3351 = eq_tm a1 a2  in
                        eq_inj acc uu____3351) Equal) uu____3233
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3365 =
          let uu____3382 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3382 head_and_args  in
        match uu____3365 with
        | (head1,args1) ->
            let uu____3435 =
              let uu____3452 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3452 head_and_args  in
            (match uu____3435 with
             | (head2,args2) ->
                 let uu____3505 =
                   let uu____3510 =
                     let uu____3511 = un_uinst head1  in
                     uu____3511.FStar_Syntax_Syntax.n  in
                   let uu____3514 =
                     let uu____3515 = un_uinst head2  in
                     uu____3515.FStar_Syntax_Syntax.n  in
                   (uu____3510, uu____3514)  in
                 (match uu____3505 with
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
                  | uu____3542 -> FStar_Pervasives_Native.None))
         in
      let t12 = unmeta t11  in
      let t22 = unmeta t21  in
      match ((t12.FStar_Syntax_Syntax.n), (t22.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3560,uu____3561) ->
          let uu____3562 = unlazy t12  in eq_tm uu____3562 t22
      | (uu____3563,FStar_Syntax_Syntax.Tm_lazy uu____3564) ->
          let uu____3565 = unlazy t22  in eq_tm t12 uu____3565
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          let uu____3568 = FStar_Syntax_Syntax.bv_eq a b  in
          equal_if uu____3568
      | uu____3570 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3594 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3594
            (fun uu____3642  ->
               match uu____3642 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3657 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3657
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3671 = eq_tm f g  in
          eq_and uu____3671
            (fun uu____3674  ->
               let uu____3675 = eq_univs_list us vs  in equal_if uu____3675)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3677),uu____3678) -> Unknown
      | (uu____3679,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3680)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3683 = FStar_Const.eq_const c d  in equal_iff uu____3683
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3686)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3688))) ->
          let uu____3717 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3717
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3771 =
            let uu____3776 =
              let uu____3777 = un_uinst h1  in
              uu____3777.FStar_Syntax_Syntax.n  in
            let uu____3780 =
              let uu____3781 = un_uinst h2  in
              uu____3781.FStar_Syntax_Syntax.n  in
            (uu____3776, uu____3780)  in
          (match uu____3771 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3787 =
                    let uu____3789 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3789  in
                  FStar_List.mem uu____3787 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3791 ->
               let uu____3796 = eq_tm h1 h2  in
               eq_and uu____3796 (fun uu____3798  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t13,bs1),FStar_Syntax_Syntax.Tm_match
         (t23,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3904 = FStar_List.zip bs1 bs2  in
            let uu____3967 = eq_tm t13 t23  in
            FStar_List.fold_right
              (fun uu____4004  ->
                 fun a  ->
                   match uu____4004 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4097  -> branch_matches b1 b2))
              uu____3904 uu____3967
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v) ->
          let uu____4102 = eq_univs u v  in equal_if uu____4102
      | (FStar_Syntax_Syntax.Tm_quoted (t13,q1),FStar_Syntax_Syntax.Tm_quoted
         (t23,q2)) ->
          let uu____4116 = eq_quoteinfo q1 q2  in
          eq_and uu____4116 (fun uu____4118  -> eq_tm t13 t23)
      | (FStar_Syntax_Syntax.Tm_refine
         (t13,phi1),FStar_Syntax_Syntax.Tm_refine (t23,phi2)) ->
          let uu____4131 =
            eq_tm t13.FStar_Syntax_Syntax.sort t23.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4131 (fun uu____4133  -> eq_tm phi1 phi2)
      | uu____4134 -> Unknown

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
      | ([],uu____4206) -> NotEqual
      | (uu____4237,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          let uu____4326 =
            let uu____4328 = FStar_Syntax_Syntax.bv_eq x1 x2  in
            Prims.op_Negation uu____4328  in
          if uu____4326
          then NotEqual
          else
            (let uu____4333 = eq_tm t1 t2  in
             match uu____4333 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4334 = eq_antiquotes a11 a21  in
                 (match uu____4334 with
                  | NotEqual  -> NotEqual
                  | uu____4335 -> Unknown)
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
        | (uu____4419,uu____4420) -> false  in
      let uu____4430 = b1  in
      match uu____4430 with
      | (p1,w1,t1) ->
          let uu____4464 = b2  in
          (match uu____4464 with
           | (p2,w2,t2) ->
               let uu____4498 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4498
               then
                 let uu____4501 =
                   (let uu____4505 = eq_tm t1 t2  in uu____4505 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4514 = eq_tm t11 t21  in
                             uu____4514 = Equal) w1 w2)
                    in
                 (if uu____4501 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4579)::a11,(b,uu____4582)::b1) ->
          let uu____4656 = eq_tm a b  in
          (match uu____4656 with
           | Equal  -> eq_args a11 b1
           | uu____4657 -> Unknown)
      | uu____4658 -> Unknown

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
      | (FStar_Pervasives_Native.None ,uu____4713) -> NotEqual
      | (uu____4720,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4750 -> NotEqual
  
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4767) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4773,uu____4774) ->
        unrefine t2
    | uu____4815 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4823 =
      let uu____4824 = FStar_Syntax_Subst.compress t  in
      uu____4824.FStar_Syntax_Syntax.n  in
    match uu____4823 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4828 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4843) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4848 ->
        let uu____4865 =
          let uu____4866 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4866 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4865 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4929,uu____4930) ->
        is_uvar t1
    | uu____4971 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4980 =
      let uu____4981 = unrefine t  in uu____4981.FStar_Syntax_Syntax.n  in
    match uu____4980 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head,uu____4987) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5013) -> is_unit t1
    | uu____5018 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5027 =
      let uu____5028 = FStar_Syntax_Subst.compress t  in
      uu____5028.FStar_Syntax_Syntax.n  in
    match uu____5027 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5033 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5042 =
      let uu____5043 = FStar_Syntax_Subst.compress e  in
      uu____5043.FStar_Syntax_Syntax.n  in
    match uu____5042 with
    | FStar_Syntax_Syntax.Tm_abs uu____5047 -> true
    | uu____5067 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5076 =
      let uu____5077 = FStar_Syntax_Subst.compress t  in
      uu____5077.FStar_Syntax_Syntax.n  in
    match uu____5076 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5081 -> true
    | uu____5097 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5107) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5113,uu____5114) ->
        pre_typ t2
    | uu____5155 -> t1
  
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
      let uu____5180 =
        let uu____5181 = un_uinst typ1  in uu____5181.FStar_Syntax_Syntax.n
         in
      match uu____5180 with
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let head1 = un_uinst head  in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5246 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5276 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5297,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5304) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5309,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5320,uu____5321,uu____5322,uu____5323,uu____5324) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5334,uu____5335,uu____5336,uu____5337) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5343,uu____5344,uu____5345,uu____5346,uu____5347) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5355,uu____5356) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5358,uu____5359) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5361 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5362 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5363 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5364 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5377 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____5388 -> []
  
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
                let uu___1004_6001 = rc  in
                let uu____6002 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1004_6001.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6002;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1004_6001.FStar_Syntax_Syntax.residual_flags)
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
            let uu___1131_7325 = rc  in
            let uu____7326 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1131_7325.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7326;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1131_7325.FStar_Syntax_Syntax.residual_flags)
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
      let uu____8378 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left
        (fun uu____8395  -> FStar_Syntax_Syntax.U_unif uu____8395) uu____8378
       in
    let uu____8396 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8396, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8409 = eq_tm a a'  in
      match uu____8409 with | Equal  -> true | uu____8412 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8417 =
    let uu____8424 =
      let uu____8425 =
        let uu____8426 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8426
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8425  in
    FStar_Syntax_Syntax.mk uu____8424  in
  uu____8417 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8539 =
            let uu____8542 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8543 =
              let uu____8550 =
                let uu____8551 =
                  let uu____8568 =
                    let uu____8579 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8588 =
                      let uu____8599 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8599]  in
                    uu____8579 :: uu____8588  in
                  (tand, uu____8568)  in
                FStar_Syntax_Syntax.Tm_app uu____8551  in
              FStar_Syntax_Syntax.mk uu____8550  in
            uu____8543 FStar_Pervasives_Native.None uu____8542  in
          FStar_Pervasives_Native.Some uu____8539
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8676 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8677 =
          let uu____8684 =
            let uu____8685 =
              let uu____8702 =
                let uu____8713 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8722 =
                  let uu____8733 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8733]  in
                uu____8713 :: uu____8722  in
              (op_t, uu____8702)  in
            FStar_Syntax_Syntax.Tm_app uu____8685  in
          FStar_Syntax_Syntax.mk uu____8684  in
        uu____8677 FStar_Pervasives_Native.None uu____8676
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8790 =
      let uu____8797 =
        let uu____8798 =
          let uu____8815 =
            let uu____8826 = FStar_Syntax_Syntax.as_arg phi  in [uu____8826]
             in
          (t_not, uu____8815)  in
        FStar_Syntax_Syntax.Tm_app uu____8798  in
      FStar_Syntax_Syntax.mk uu____8797  in
    uu____8790 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____9023 =
      let uu____9030 =
        let uu____9031 =
          let uu____9048 =
            let uu____9059 = FStar_Syntax_Syntax.as_arg e  in [uu____9059]
             in
          (b2t_v, uu____9048)  in
        FStar_Syntax_Syntax.Tm_app uu____9031  in
      FStar_Syntax_Syntax.mk uu____9030  in
    uu____9023 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9106 = head_and_args e  in
    match uu____9106 with
    | (hd,args) ->
        let uu____9151 =
          let uu____9166 =
            let uu____9167 = FStar_Syntax_Subst.compress hd  in
            uu____9167.FStar_Syntax_Syntax.n  in
          (uu____9166, args)  in
        (match uu____9151 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9184)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9219 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9241 =
      let uu____9242 = unmeta t  in uu____9242.FStar_Syntax_Syntax.n  in
    match uu____9241 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9247 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9270 = is_t_true t1  in
      if uu____9270
      then t2
      else
        (let uu____9277 = is_t_true t2  in
         if uu____9277 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9305 = is_t_true t1  in
      if uu____9305
      then t_true
      else
        (let uu____9312 = is_t_true t2  in
         if uu____9312 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9341 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9342 =
        let uu____9349 =
          let uu____9350 =
            let uu____9367 =
              let uu____9378 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9387 =
                let uu____9398 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9398]  in
              uu____9378 :: uu____9387  in
            (teq, uu____9367)  in
          FStar_Syntax_Syntax.Tm_app uu____9350  in
        FStar_Syntax_Syntax.mk uu____9349  in
      uu____9342 FStar_Pervasives_Native.None uu____9341
  
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
          let uu____9465 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9466 =
            let uu____9473 =
              let uu____9474 =
                let uu____9491 =
                  let uu____9502 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9511 =
                    let uu____9522 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9531 =
                      let uu____9542 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9542]  in
                    uu____9522 :: uu____9531  in
                  uu____9502 :: uu____9511  in
                (eq_inst, uu____9491)  in
              FStar_Syntax_Syntax.Tm_app uu____9474  in
            FStar_Syntax_Syntax.mk uu____9473  in
          uu____9466 FStar_Pervasives_Native.None uu____9465
  
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
        let uu____9619 =
          let uu____9626 =
            let uu____9627 =
              let uu____9644 =
                let uu____9655 = FStar_Syntax_Syntax.iarg t  in
                let uu____9664 =
                  let uu____9675 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9684 =
                    let uu____9695 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9695]  in
                  uu____9675 :: uu____9684  in
                uu____9655 :: uu____9664  in
              (t_has_type1, uu____9644)  in
            FStar_Syntax_Syntax.Tm_app uu____9627  in
          FStar_Syntax_Syntax.mk uu____9626  in
        uu____9619 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9772 =
          let uu____9779 =
            let uu____9780 =
              let uu____9797 =
                let uu____9808 = FStar_Syntax_Syntax.iarg t  in
                let uu____9817 =
                  let uu____9828 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9828]  in
                uu____9808 :: uu____9817  in
              (t_with_type1, uu____9797)  in
            FStar_Syntax_Syntax.Tm_app uu____9780  in
          FStar_Syntax_Syntax.mk uu____9779  in
        uu____9772 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9875 =
    let uu____9882 =
      let uu____9883 =
        let uu____9890 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9890, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9883  in
    FStar_Syntax_Syntax.mk uu____9882  in
  uu____9875 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
        let uu____9973 =
          let uu____9980 =
            let uu____9981 =
              let uu____9998 =
                let uu____10009 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____10018 =
                  let uu____10029 =
                    let uu____10038 =
                      let uu____10039 =
                        let uu____10040 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10040]  in
                      abs uu____10039 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10038  in
                  [uu____10029]  in
                uu____10009 :: uu____10018  in
              (fa, uu____9998)  in
            FStar_Syntax_Syntax.Tm_app uu____9981  in
          FStar_Syntax_Syntax.mk uu____9980  in
        uu____9973 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10167 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10167
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10186 -> true
    | uu____10188 -> false
  
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
          let uu____10235 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10235, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10264 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10264, FStar_Pervasives_Native.None, t2)  in
        let uu____10278 =
          let uu____10279 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10279  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10278
  
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
      let uu____10355 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10358 =
        let uu____10369 = FStar_Syntax_Syntax.as_arg p  in [uu____10369]  in
      mk_app uu____10355 uu____10358
  
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
      let uu____10409 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10412 =
        let uu____10423 = FStar_Syntax_Syntax.as_arg p  in [uu____10423]  in
      mk_app uu____10409 uu____10412
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10458 = head_and_args t  in
    match uu____10458 with
    | (head,args) ->
        let head1 = unascribe head  in
        let head2 = un_uinst head1  in
        let uu____10507 =
          let uu____10522 =
            let uu____10523 = FStar_Syntax_Subst.compress head2  in
            uu____10523.FStar_Syntax_Syntax.n  in
          (uu____10522, args)  in
        (match uu____10507 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10542)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10608 =
                    let uu____10613 =
                      let uu____10614 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10614]  in
                    FStar_Syntax_Subst.open_term uu____10613 p  in
                  (match uu____10608 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10671 -> failwith "impossible"  in
                       let uu____10679 =
                         let uu____10681 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10681
                          in
                       if uu____10679
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10697 -> FStar_Pervasives_Native.None)
         | uu____10700 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10731 = head_and_args t  in
    match uu____10731 with
    | (head,args) ->
        let uu____10782 =
          let uu____10797 =
            let uu____10798 = FStar_Syntax_Subst.compress head  in
            uu____10798.FStar_Syntax_Syntax.n  in
          (uu____10797, args)  in
        (match uu____10782 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10820;
               FStar_Syntax_Syntax.vars = uu____10821;_},u::[]),(t1,uu____10824)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10871 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10906 = head_and_args t  in
    match uu____10906 with
    | (head,args) ->
        let uu____10957 =
          let uu____10972 =
            let uu____10973 = FStar_Syntax_Subst.compress head  in
            uu____10973.FStar_Syntax_Syntax.n  in
          (uu____10972, args)  in
        (match uu____10957 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10995;
               FStar_Syntax_Syntax.vars = uu____10996;_},u::[]),(t1,uu____10999)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11046 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11074 =
      let uu____11091 = unmeta t  in head_and_args uu____11091  in
    match uu____11074 with
    | (head,uu____11094) ->
        let uu____11119 =
          let uu____11120 = un_uinst head  in
          uu____11120.FStar_Syntax_Syntax.n  in
        (match uu____11119 with
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
         | uu____11125 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11145 =
      let uu____11146 = FStar_Syntax_Subst.compress t  in
      uu____11146.FStar_Syntax_Syntax.n  in
    match uu____11145 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11252 =
          let uu____11257 =
            let uu____11258 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11258  in
          (b, uu____11257)  in
        FStar_Pervasives_Native.Some uu____11252
    | uu____11263 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11286 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11286
      (fun uu____11314  ->
         match uu____11314 with
         | (b,c) ->
             let uu____11333 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11333 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11396 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11433 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11433
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11485 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11528 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11569 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11955) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11967) ->
          unmeta_monadic t
      | uu____11980 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12049 =
        match uu____12049 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12087  ->
                   match uu____12087 with
                   | (lid,out_lid) ->
                       let uu____12096 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12096
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12123 = head_and_args t  in
      match uu____12123 with
      | (hd,args) ->
          let uu____12168 =
            let uu____12169 = un_uinst hd  in
            uu____12169.FStar_Syntax_Syntax.n  in
          (match uu____12168 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12175 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12184 = un_squash t  in
      FStar_Util.bind_opt uu____12184
        (fun t1  ->
           let uu____12200 = head_and_args' t1  in
           match uu____12200 with
           | (hd,args) ->
               let uu____12239 =
                 let uu____12240 = un_uinst hd  in
                 uu____12240.FStar_Syntax_Syntax.n  in
               (match uu____12239 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12246 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12287,pats)) ->
          let uu____12325 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12325)
      | uu____12338 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12405 = head_and_args t1  in
        match uu____12405 with
        | (t2,args) ->
            let uu____12460 = un_uinst t2  in
            let uu____12461 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12502  ->
                      match uu____12502 with
                      | (t3,imp) ->
                          let uu____12521 = unascribe t3  in
                          (uu____12521, imp)))
               in
            (uu____12460, uu____12461)
         in
      let rec aux qopt out t1 =
        let uu____12572 = let uu____12596 = flat t1  in (qopt, uu____12596)
           in
        match uu____12572 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12636;
                 FStar_Syntax_Syntax.vars = uu____12637;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12640);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12641;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12642;_},uu____12643)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12745;
                 FStar_Syntax_Syntax.vars = uu____12746;_},uu____12747::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12750);
                  FStar_Syntax_Syntax.pos = uu____12751;
                  FStar_Syntax_Syntax.vars = uu____12752;_},uu____12753)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12870;
               FStar_Syntax_Syntax.vars = uu____12871;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12874);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12875;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12876;_},uu____12877)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12970 =
              let uu____12974 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12974  in
            aux uu____12970 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12984;
               FStar_Syntax_Syntax.vars = uu____12985;_},uu____12986::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12989);
                FStar_Syntax_Syntax.pos = uu____12990;
                FStar_Syntax_Syntax.vars = uu____12991;_},uu____12992)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13101 =
              let uu____13105 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13105  in
            aux uu____13101 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13115) ->
            let bs = FStar_List.rev out  in
            let uu____13168 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13168 with
             | (bs1,t2) ->
                 let uu____13177 = patterns t2  in
                 (match uu____13177 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13227 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13282 = un_squash t  in
      FStar_Util.bind_opt uu____13282
        (fun t1  ->
           let uu____13297 = arrow_one t1  in
           match uu____13297 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13312 =
                 let uu____13314 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13314  in
               if uu____13312
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13324 = comp_to_comp_typ_nouniv c  in
                    uu____13324.FStar_Syntax_Syntax.result_typ  in
                  let uu____13325 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13325
                  then
                    let uu____13332 = patterns q  in
                    match uu____13332 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13395 =
                       let uu____13396 =
                         let uu____13401 =
                           let uu____13402 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13413 =
                             let uu____13424 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13424]  in
                           uu____13402 :: uu____13413  in
                         (FStar_Parser_Const.imp_lid, uu____13401)  in
                       BaseConn uu____13396  in
                     FStar_Pervasives_Native.Some uu____13395))
           | uu____13457 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13465 = un_squash t  in
      FStar_Util.bind_opt uu____13465
        (fun t1  ->
           let uu____13496 = head_and_args' t1  in
           match uu____13496 with
           | (hd,args) ->
               let uu____13535 =
                 let uu____13550 =
                   let uu____13551 = un_uinst hd  in
                   uu____13551.FStar_Syntax_Syntax.n  in
                 (uu____13550, args)  in
               (match uu____13535 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13568)::(a2,uu____13570)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13621 =
                      let uu____13622 = FStar_Syntax_Subst.compress a2  in
                      uu____13622.FStar_Syntax_Syntax.n  in
                    (match uu____13621 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13629) ->
                         let uu____13664 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13664 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13717 -> failwith "impossible"  in
                              let uu____13725 = patterns q1  in
                              (match uu____13725 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13786 -> FStar_Pervasives_Native.None)
                | uu____13787 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13810 = destruct_sq_forall phi  in
          (match uu____13810 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13820  ->
                    FStar_Pervasives_Native.Some uu____13820)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13827 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13833 = destruct_sq_exists phi  in
          (match uu____13833 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13843  ->
                    FStar_Pervasives_Native.Some uu____13843)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13850 -> f1)
      | uu____13853 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13857 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13857
      (fun uu____13862  ->
         let uu____13863 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13863
           (fun uu____13868  ->
              let uu____13869 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13869
                (fun uu____13874  ->
                   let uu____13875 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13875
                     (fun uu____13880  ->
                        let uu____13881 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13881
                          (fun uu____13885  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13903 =
            let uu____13908 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13908  in
          let uu____13909 =
            let uu____13910 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13910  in
          let uu____13913 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13903 a.FStar_Syntax_Syntax.action_univs uu____13909
            FStar_Parser_Const.effect_Tot_lid uu____13913 [] pos
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
    let uu____13939 =
      let uu____13946 =
        let uu____13947 =
          let uu____13964 =
            let uu____13975 = FStar_Syntax_Syntax.as_arg t  in [uu____13975]
             in
          (reify_, uu____13964)  in
        FStar_Syntax_Syntax.Tm_app uu____13947  in
      FStar_Syntax_Syntax.mk uu____13946  in
    uu____13939 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14027 =
        let uu____14034 =
          let uu____14035 =
            let uu____14036 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14036  in
          FStar_Syntax_Syntax.Tm_constant uu____14035  in
        FStar_Syntax_Syntax.mk uu____14034  in
      uu____14027 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14038 =
      let uu____14045 =
        let uu____14046 =
          let uu____14063 =
            let uu____14074 = FStar_Syntax_Syntax.as_arg t  in [uu____14074]
             in
          (reflect_, uu____14063)  in
        FStar_Syntax_Syntax.Tm_app uu____14046  in
      FStar_Syntax_Syntax.mk uu____14045  in
    uu____14038 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14118 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14135 = unfold_lazy i  in delta_qualifier uu____14135
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14137 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14138 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14139 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14162 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14175 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14176 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14183 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14184 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14200) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14205;
           FStar_Syntax_Syntax.index = uu____14206;
           FStar_Syntax_Syntax.sort = t2;_},uu____14208)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14217) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14223,uu____14224) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14266) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14291,t2,uu____14293) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14318,t2) -> delta_qualifier t2
  
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
    let uu____14357 = delta_qualifier t  in incr_delta_depth uu____14357
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14365 =
      let uu____14366 = FStar_Syntax_Subst.compress t  in
      uu____14366.FStar_Syntax_Syntax.n  in
    match uu____14365 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14371 -> false
  
let rec apply_last :
  'uuuuuu14380 .
    ('uuuuuu14380 -> 'uuuuuu14380) ->
      'uuuuuu14380 Prims.list -> 'uuuuuu14380 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14406 = f a  in [uu____14406]
      | x::xs -> let uu____14411 = apply_last f xs  in x :: uu____14411
  
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
          let uu____14466 =
            let uu____14473 =
              let uu____14474 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14474  in
            FStar_Syntax_Syntax.mk uu____14473  in
          uu____14466 FStar_Pervasives_Native.None rng  in
        let cons args pos =
          let uu____14488 =
            let uu____14493 =
              let uu____14494 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14494
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14493 args  in
          uu____14488 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14508 =
            let uu____14513 =
              let uu____14514 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14514
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14513 args  in
          uu____14508 FStar_Pervasives_Native.None pos  in
        let uu____14515 =
          let uu____14516 =
            let uu____14517 = FStar_Syntax_Syntax.iarg typ  in [uu____14517]
             in
          nil uu____14516 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14551 =
                 let uu____14552 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14561 =
                   let uu____14572 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14581 =
                     let uu____14592 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14592]  in
                   uu____14572 :: uu____14581  in
                 uu____14552 :: uu____14561  in
               cons uu____14551 t.FStar_Syntax_Syntax.pos) l uu____14515
  
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
        | uu____14701 -> false
  
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
          | uu____14815 -> false
  
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
        | uu____14981 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15019 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15019
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
        let t11 = let uu____15223 = unmeta_safe t1  in canon_app uu____15223
           in
        let t21 = let uu____15229 = unmeta_safe t2  in canon_app uu____15229
           in
        let uu____15232 =
          let uu____15237 =
            let uu____15238 =
              let uu____15241 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15241  in
            uu____15238.FStar_Syntax_Syntax.n  in
          let uu____15242 =
            let uu____15243 =
              let uu____15246 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15246  in
            uu____15243.FStar_Syntax_Syntax.n  in
          (uu____15237, uu____15242)  in
        match uu____15232 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15248,uu____15249) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15258,FStar_Syntax_Syntax.Tm_uinst uu____15259) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15268,uu____15269) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15286,FStar_Syntax_Syntax.Tm_delayed uu____15287) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15304,uu____15305) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15334,FStar_Syntax_Syntax.Tm_ascribed uu____15335) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15374 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15374
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15379 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15379
        | (FStar_Syntax_Syntax.Tm_type
           uu____15382,FStar_Syntax_Syntax.Tm_type uu____15383) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15441 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15441) &&
              (let uu____15451 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15451)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15500 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15500) &&
              (let uu____15510 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15510)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15527 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15527) &&
              (let uu____15531 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15531)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15588 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15588) &&
              (let uu____15592 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15592)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15681 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15681) &&
              (let uu____15685 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15685)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15702,uu____15703) ->
            let uu____15704 =
              let uu____15706 = unlazy t11  in
              term_eq_dbg dbg uu____15706 t21  in
            check "lazy_l" uu____15704
        | (uu____15708,FStar_Syntax_Syntax.Tm_lazy uu____15709) ->
            let uu____15710 =
              let uu____15712 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15712  in
            check "lazy_r" uu____15710
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15757 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15757))
              &&
              (let uu____15761 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15761)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15765),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15767)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15825 =
               let uu____15827 = eq_quoteinfo qi1 qi2  in uu____15827 = Equal
                in
             check "tm_quoted qi" uu____15825) &&
              (let uu____15830 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15830)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15860 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15860) &&
                   (let uu____15864 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15864)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15883 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15883) &&
                    (let uu____15887 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15887))
                   &&
                   (let uu____15891 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15891)
             | uu____15894 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15900) -> fail "unk"
        | (uu____15902,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15904,uu____15905) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15907,uu____15908) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15910,uu____15911) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15913,uu____15914) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15916,uu____15917) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15919,uu____15920) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15940,uu____15941) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15957,uu____15958) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15966,uu____15967) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15985,uu____15986) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16010,uu____16011) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16026,uu____16027) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16041,uu____16042) ->
            fail "bottom"
        | (uu____16050,FStar_Syntax_Syntax.Tm_bvar uu____16051) ->
            fail "bottom"
        | (uu____16053,FStar_Syntax_Syntax.Tm_name uu____16054) ->
            fail "bottom"
        | (uu____16056,FStar_Syntax_Syntax.Tm_fvar uu____16057) ->
            fail "bottom"
        | (uu____16059,FStar_Syntax_Syntax.Tm_constant uu____16060) ->
            fail "bottom"
        | (uu____16062,FStar_Syntax_Syntax.Tm_type uu____16063) ->
            fail "bottom"
        | (uu____16065,FStar_Syntax_Syntax.Tm_abs uu____16066) ->
            fail "bottom"
        | (uu____16086,FStar_Syntax_Syntax.Tm_arrow uu____16087) ->
            fail "bottom"
        | (uu____16103,FStar_Syntax_Syntax.Tm_refine uu____16104) ->
            fail "bottom"
        | (uu____16112,FStar_Syntax_Syntax.Tm_app uu____16113) ->
            fail "bottom"
        | (uu____16131,FStar_Syntax_Syntax.Tm_match uu____16132) ->
            fail "bottom"
        | (uu____16156,FStar_Syntax_Syntax.Tm_let uu____16157) ->
            fail "bottom"
        | (uu____16172,FStar_Syntax_Syntax.Tm_uvar uu____16173) ->
            fail "bottom"
        | (uu____16187,FStar_Syntax_Syntax.Tm_meta uu____16188) ->
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
               let uu____16223 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16223)
          (fun q1  ->
             fun q2  ->
               let uu____16235 =
                 let uu____16237 = eq_aqual q1 q2  in uu____16237 = Equal  in
               check "arg qual" uu____16235) a1 a2

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
               let uu____16262 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16262)
          (fun q1  ->
             fun q2  ->
               let uu____16274 =
                 let uu____16276 = eq_aqual q1 q2  in uu____16276 = Equal  in
               check "binder qual" uu____16274) b1 b2

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
        ((let uu____16290 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16290) &&
           (let uu____16294 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16294))
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
    fun uu____16304  ->
      fun uu____16305  ->
        match (uu____16304, uu____16305) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16432 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16432) &&
               (let uu____16436 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16436))
              &&
              (let uu____16440 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16482 -> false  in
               check "branch when" uu____16440)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16503 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16503) &&
           (let uu____16512 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16512))
          &&
          (let uu____16516 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16516)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16533 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16533 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16587 ->
        let uu____16602 =
          let uu____16604 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16604  in
        Prims.int_one + uu____16602
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16607 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16607
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16611 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16611
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16620 = sizeof t1  in (FStar_List.length us) + uu____16620
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16624) ->
        let uu____16649 = sizeof t1  in
        let uu____16651 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16666  ->
                 match uu____16666 with
                 | (bv,uu____16676) ->
                     let uu____16681 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16681) Prims.int_zero bs
           in
        uu____16649 + uu____16651
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____16710 = sizeof hd  in
        let uu____16712 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16727  ->
                 match uu____16727 with
                 | (arg,uu____16737) ->
                     let uu____16742 = sizeof arg  in acc + uu____16742)
            Prims.int_zero args
           in
        uu____16710 + uu____16712
    | uu____16745 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16759 =
        let uu____16760 = un_uinst t  in uu____16760.FStar_Syntax_Syntax.n
         in
      match uu____16759 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16765 -> false
  
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
           let uu____16826 = head_and_args t  in
           match uu____16826 with
           | (head,args) ->
               let uu____16881 =
                 let uu____16882 = FStar_Syntax_Subst.compress head  in
                 uu____16882.FStar_Syntax_Syntax.n  in
               (match uu____16881 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16908 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____16941 = is_fvar attr a  in Prims.op_Negation uu____16941)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options s =
        let uu____16962 = FStar_Options.set_options s  in
        match uu____16962 with
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
          ((let uu____16976 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16976 (fun uu____16978  -> ()));
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
          let uu____16992 = FStar_Options.internal_pop ()  in
          if uu____16992
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
    | FStar_Syntax_Syntax.Tm_delayed uu____17024 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17043 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17058 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17059 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17060 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17069) ->
        let uu____17094 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17094 with
         | (bs1,t2) ->
             let uu____17103 =
               FStar_List.collect
                 (fun uu____17115  ->
                    match uu____17115 with
                    | (b,uu____17125) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17130 = unbound_variables t2  in
             FStar_List.append uu____17103 uu____17130)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17155 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17155 with
         | (bs1,c1) ->
             let uu____17164 =
               FStar_List.collect
                 (fun uu____17176  ->
                    match uu____17176 with
                    | (b,uu____17186) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17191 = unbound_variables_comp c1  in
             FStar_List.append uu____17164 uu____17191)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17200 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17200 with
         | (bs,t2) ->
             let uu____17223 =
               FStar_List.collect
                 (fun uu____17235  ->
                    match uu____17235 with
                    | (b1,uu____17245) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17250 = unbound_variables t2  in
             FStar_List.append uu____17223 uu____17250)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17279 =
          FStar_List.collect
            (fun uu____17293  ->
               match uu____17293 with
               | (x,uu____17305) -> unbound_variables x) args
           in
        let uu____17314 = unbound_variables t1  in
        FStar_List.append uu____17279 uu____17314
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17355 = unbound_variables t1  in
        let uu____17358 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17373 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17373 with
                  | (p,wopt,t2) ->
                      let uu____17395 = unbound_variables t2  in
                      let uu____17398 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17395 uu____17398))
           in
        FStar_List.append uu____17355 uu____17358
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17412) ->
        let uu____17453 = unbound_variables t1  in
        let uu____17456 =
          let uu____17459 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17490 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17459 uu____17490  in
        FStar_List.append uu____17453 uu____17456
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17531 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17534 =
          let uu____17537 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17540 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17545 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17547 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17547 with
                 | (uu____17568,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17537 uu____17540  in
        FStar_List.append uu____17531 uu____17534
    | FStar_Syntax_Syntax.Tm_let ((uu____17570,lbs),t1) ->
        let uu____17590 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17590 with
         | (lbs1,t2) ->
             let uu____17605 = unbound_variables t2  in
             let uu____17608 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17615 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17618 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17615 uu____17618) lbs1
                in
             FStar_List.append uu____17605 uu____17608)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17635 = unbound_variables t1  in
        let uu____17638 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17643,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17698  ->
                      match uu____17698 with
                      | (a,uu____17710) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17719,uu____17720,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17726,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17732 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17741 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17742 -> []  in
        FStar_List.append uu____17635 uu____17638

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17749) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17759) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17769 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17772 =
          FStar_List.collect
            (fun uu____17786  ->
               match uu____17786 with
               | (a,uu____17798) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17769 uu____17772

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
            let uu____17913 = head_and_args h  in
            (match uu____17913 with
             | (head,args) ->
                 let uu____17974 =
                   let uu____17975 = FStar_Syntax_Subst.compress head  in
                   uu____17975.FStar_Syntax_Syntax.n  in
                 (match uu____17974 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18028 -> aux (h :: acc) t))
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
      let uu____18052 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18052 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2486_18094 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2486_18094.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2486_18094.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2486_18094.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2486_18094.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2486_18094.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18102 =
      let uu____18103 = FStar_Syntax_Subst.compress t  in
      uu____18103.FStar_Syntax_Syntax.n  in
    match uu____18102 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18107,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18135)::uu____18136 ->
                  let pats' = unmeta pats  in
                  let uu____18196 = head_and_args pats'  in
                  (match uu____18196 with
                   | (head,uu____18215) ->
                       let uu____18240 =
                         let uu____18241 = un_uinst head  in
                         uu____18241.FStar_Syntax_Syntax.n  in
                       (match uu____18240 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18246 -> false))
              | uu____18248 -> false)
         | uu____18260 -> false)
    | uu____18262 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18278 =
      let uu____18295 = unmeta e  in head_and_args uu____18295  in
    match uu____18278 with
    | (head,args) ->
        let uu____18326 =
          let uu____18341 =
            let uu____18342 = un_uinst head  in
            uu____18342.FStar_Syntax_Syntax.n  in
          (uu____18341, args)  in
        (match uu____18326 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18360) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18384::(hd,uu____18386)::(tl,uu____18388)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18455 =
               let uu____18458 =
                 let uu____18461 = list_elements tl  in
                 FStar_Util.must uu____18461  in
               hd :: uu____18458  in
             FStar_Pervasives_Native.Some uu____18455
         | uu____18470 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18499 =
      let uu____18500 = FStar_Syntax_Subst.compress t  in
      uu____18500.FStar_Syntax_Syntax.n  in
    match uu____18499 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18507) ->
        let uu____18542 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18542 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18576 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18576
             then
               let uu____18583 =
                 let uu____18594 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18594]  in
               mk_app t uu____18583
             else e1)
    | uu____18621 ->
        let uu____18622 =
          let uu____18633 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18633]  in
        mk_app t uu____18622
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18688 = list_elements e  in
        match uu____18688 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18723 =
          let uu____18740 = unmeta p  in
          FStar_All.pipe_right uu____18740 head_and_args  in
        match uu____18723 with
        | (head,args) ->
            let uu____18791 =
              let uu____18806 =
                let uu____18807 = un_uinst head  in
                uu____18807.FStar_Syntax_Syntax.n  in
              (uu____18806, args)  in
            (match uu____18791 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18829,uu____18830)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18882 ->
                 let uu____18897 =
                   let uu____18903 =
                     let uu____18905 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18905
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____18903)  in
                 FStar_Errors.raise_error uu____18897
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____18948 =
            let uu____18965 = unmeta t1  in
            FStar_All.pipe_right uu____18965 head_and_args  in
          match uu____18948 with
          | (head,args) ->
              let uu____19012 =
                let uu____19027 =
                  let uu____19028 = un_uinst head  in
                  uu____19028.FStar_Syntax_Syntax.n  in
                (uu____19027, args)  in
              (match uu____19012 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19047)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19084 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19114 = smt_pat_or t1  in
            (match uu____19114 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19136 = list_elements1 e  in
                 FStar_All.pipe_right uu____19136
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19166 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19166
                           (FStar_List.map one_pat)))
             | uu____19195 ->
                 let uu____19200 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19200])
        | uu____19255 ->
            let uu____19258 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19258]
         in
      let uu____19313 =
        let uu____19346 =
          let uu____19347 = FStar_Syntax_Subst.compress t  in
          uu____19347.FStar_Syntax_Syntax.n  in
        match uu____19346 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19404 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19404 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19475;
                        FStar_Syntax_Syntax.effect_name = uu____19476;
                        FStar_Syntax_Syntax.result_typ = uu____19477;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19479)::(post,uu____19481)::(pats,uu____19483)::[];
                        FStar_Syntax_Syntax.flags = uu____19484;_}
                      ->
                      let uu____19545 = lemma_pats pats  in
                      (binders1, pre, post, uu____19545)
                  | uu____19582 -> failwith "impos"))
        | uu____19616 -> failwith "Impos"  in
      match uu____19313 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19708 =
              let uu____19715 =
                let uu____19716 =
                  let uu____19723 = mk_imp pre post1  in
                  let uu____19726 =
                    let uu____19727 =
                      let uu____19748 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19748, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19727  in
                  (uu____19723, uu____19726)  in
                FStar_Syntax_Syntax.Tm_meta uu____19716  in
              FStar_Syntax_Syntax.mk uu____19715  in
            uu____19708 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19772 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19772 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19802 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19813 -> true
    | uu____19815 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19826 -> true
    | uu____19828 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19846 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19847 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19848 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19849 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19850 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19851 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19852 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19853 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19856 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19859 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19846;
        FStar_Syntax_Syntax.bind_wp = uu____19847;
        FStar_Syntax_Syntax.stronger = uu____19848;
        FStar_Syntax_Syntax.if_then_else = uu____19849;
        FStar_Syntax_Syntax.ite_wp = uu____19850;
        FStar_Syntax_Syntax.close_wp = uu____19851;
        FStar_Syntax_Syntax.trivial = uu____19852;
        FStar_Syntax_Syntax.repr = uu____19853;
        FStar_Syntax_Syntax.return_repr = uu____19856;
        FStar_Syntax_Syntax.bind_repr = uu____19859
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____19891 =
        match uu____19891 with
        | (ts1,ts2) ->
            let uu____19902 = f ts1  in
            let uu____19903 = f ts2  in (uu____19902, uu____19903)
         in
      let uu____19904 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____19909 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____19914 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____19919 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____19924 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____19904;
        FStar_Syntax_Syntax.l_return = uu____19909;
        FStar_Syntax_Syntax.l_bind = uu____19914;
        FStar_Syntax_Syntax.l_subcomp = uu____19919;
        FStar_Syntax_Syntax.l_if_then_else = uu____19924
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
          let uu____19946 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____19946
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19948 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____19948
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19950 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____19950
  
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
    | uu____19965 -> FStar_Pervasives_Native.None
  
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
        let uu____19979 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19979
          (fun uu____19986  -> FStar_Pervasives_Native.Some uu____19986)
  
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
        let uu____20026 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20026
          (fun uu____20033  -> FStar_Pervasives_Native.Some uu____20033)
  
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
        let uu____20047 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20047
          (fun uu____20054  -> FStar_Pervasives_Native.Some uu____20054)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20068  -> FStar_Pervasives_Native.Some uu____20068)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20072  -> FStar_Pervasives_Native.Some uu____20072)
    | uu____20073 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20085 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20085
          (fun uu____20092  -> FStar_Pervasives_Native.Some uu____20092)
    | uu____20093 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20107  -> FStar_Pervasives_Native.Some uu____20107)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20111  -> FStar_Pervasives_Native.Some uu____20111)
    | uu____20112 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20126  -> FStar_Pervasives_Native.Some uu____20126)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20130  -> FStar_Pervasives_Native.Some uu____20130)
    | uu____20131 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20155 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20156 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20158 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20158
          (fun uu____20165  -> FStar_Pervasives_Native.Some uu____20165)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun uu____20179  -> FStar_Pervasives_Native.Some uu____20179)
    | uu____20180 -> FStar_Pervasives_Native.None
  