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
      let uu____3555 =
        let uu____3560 =
          let uu____3561 = unmeta t11  in uu____3561.FStar_Syntax_Syntax.n
           in
        let uu____3564 =
          let uu____3565 = unmeta t21  in uu____3565.FStar_Syntax_Syntax.n
           in
        (uu____3560, uu____3564)  in
      match uu____3555 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3571,uu____3572) ->
          let uu____3573 = unlazy t11  in eq_tm uu____3573 t21
      | (uu____3574,FStar_Syntax_Syntax.Tm_lazy uu____3575) ->
          let uu____3576 = unlazy t21  in eq_tm t11 uu____3576
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          let uu____3579 = FStar_Syntax_Syntax.bv_eq a b  in
          equal_if uu____3579
      | uu____3581 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3605 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3605
            (fun uu____3653  ->
               match uu____3653 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3668 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3668
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3682 = eq_tm f g  in
          eq_and uu____3682
            (fun uu____3685  ->
               let uu____3686 = eq_univs_list us vs  in equal_if uu____3686)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3688),uu____3689) -> Unknown
      | (uu____3690,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3691)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3694 = FStar_Const.eq_const c d  in equal_iff uu____3694
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3697)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3699))) ->
          let uu____3728 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3728
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3782 =
            let uu____3787 =
              let uu____3788 = un_uinst h1  in
              uu____3788.FStar_Syntax_Syntax.n  in
            let uu____3791 =
              let uu____3792 = un_uinst h2  in
              uu____3792.FStar_Syntax_Syntax.n  in
            (uu____3787, uu____3791)  in
          (match uu____3782 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3798 =
                    let uu____3800 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3800  in
                  FStar_List.mem uu____3798 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3802 ->
               let uu____3807 = eq_tm h1 h2  in
               eq_and uu____3807 (fun uu____3809  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3915 = FStar_List.zip bs1 bs2  in
            let uu____3978 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____4015  ->
                 fun a  ->
                   match uu____4015 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4108  -> branch_matches b1 b2))
              uu____3915 uu____3978
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v) ->
          let uu____4113 = eq_univs u v  in equal_if uu____4113
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____4127 = eq_quoteinfo q1 q2  in
          eq_and uu____4127 (fun uu____4129  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____4142 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4142 (fun uu____4144  -> eq_tm phi1 phi2)
      | uu____4145 -> Unknown

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
      | ([],uu____4217) -> NotEqual
      | (uu____4248,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          let uu____4337 =
            let uu____4339 = FStar_Syntax_Syntax.bv_eq x1 x2  in
            Prims.op_Negation uu____4339  in
          if uu____4337
          then NotEqual
          else
            (let uu____4344 = eq_tm t1 t2  in
             match uu____4344 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4345 = eq_antiquotes a11 a21  in
                 (match uu____4345 with
                  | NotEqual  -> NotEqual
                  | uu____4346 -> Unknown)
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
        | (uu____4430,uu____4431) -> false  in
      let uu____4441 = b1  in
      match uu____4441 with
      | (p1,w1,t1) ->
          let uu____4475 = b2  in
          (match uu____4475 with
           | (p2,w2,t2) ->
               let uu____4509 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4509
               then
                 let uu____4512 =
                   (let uu____4516 = eq_tm t1 t2  in uu____4516 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4525 = eq_tm t11 t21  in
                             uu____4525 = Equal) w1 w2)
                    in
                 (if uu____4512 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4590)::a11,(b,uu____4593)::b1) ->
          let uu____4667 = eq_tm a b  in
          (match uu____4667 with
           | Equal  -> eq_args a11 b1
           | uu____4668 -> Unknown)
      | uu____4669 -> Unknown

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
      | (FStar_Pervasives_Native.None ,uu____4724) -> NotEqual
      | (uu____4731,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4761 -> NotEqual
  
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4778) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4784,uu____4785) ->
        unrefine t2
    | uu____4826 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4834 =
      let uu____4835 = FStar_Syntax_Subst.compress t  in
      uu____4835.FStar_Syntax_Syntax.n  in
    match uu____4834 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4839 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4854) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4859 ->
        let uu____4876 =
          let uu____4877 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4877 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4876 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4940,uu____4941) ->
        is_uvar t1
    | uu____4982 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4991 =
      let uu____4992 = unrefine t  in uu____4992.FStar_Syntax_Syntax.n  in
    match uu____4991 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head,uu____4998) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5024) -> is_unit t1
    | uu____5029 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5038 =
      let uu____5039 = FStar_Syntax_Subst.compress t  in
      uu____5039.FStar_Syntax_Syntax.n  in
    match uu____5038 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5044 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5053 =
      let uu____5054 = FStar_Syntax_Subst.compress e  in
      uu____5054.FStar_Syntax_Syntax.n  in
    match uu____5053 with
    | FStar_Syntax_Syntax.Tm_abs uu____5058 -> true
    | uu____5078 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5087 =
      let uu____5088 = FStar_Syntax_Subst.compress t  in
      uu____5088.FStar_Syntax_Syntax.n  in
    match uu____5087 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5092 -> true
    | uu____5108 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5118) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5124,uu____5125) ->
        pre_typ t2
    | uu____5166 -> t1
  
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
      let uu____5191 =
        let uu____5192 = un_uinst typ1  in uu____5192.FStar_Syntax_Syntax.n
         in
      match uu____5191 with
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let head1 = un_uinst head  in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5257 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5287 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5308,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5315) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5320,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5331,uu____5332,uu____5333,uu____5334,uu____5335) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5345,uu____5346,uu____5347,uu____5348) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5354,uu____5355,uu____5356,uu____5357,uu____5358) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5366,uu____5367) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5369,uu____5370) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5372 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5373 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5374 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5375 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5388 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5412 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5438  ->
    match uu___7_5438 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'uuuuuu5452 'uuuuuu5453 .
    ('uuuuuu5452 FStar_Syntax_Syntax.syntax * 'uuuuuu5453) ->
      FStar_Range.range
  =
  fun uu____5464  ->
    match uu____5464 with | (hd,uu____5472) -> hd.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'uuuuuu5486 'uuuuuu5487 .
    ('uuuuuu5486 FStar_Syntax_Syntax.syntax * 'uuuuuu5487) Prims.list ->
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
      | uu____5585 ->
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
      let uu____5644 =
        FStar_List.map
          (fun uu____5671  ->
             match uu____5671 with
             | (bv,aq) ->
                 let uu____5690 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5690, aq)) bs
         in
      mk_app f uu____5644
  
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
          (let uu____5741 =
             let uu____5747 =
               let uu____5749 =
                 let uu____5751 = FStar_Ident.ident_of_lid lid  in
                 FStar_Ident.text_of_id uu____5751  in
               mk_field_projector_name_from_string uu____5749 itext  in
             let uu____5752 = FStar_Ident.range_of_id i  in
             (uu____5747, uu____5752)  in
           FStar_Ident.mk_ident uu____5741)
         in
      let uu____5754 =
        let uu____5755 = FStar_Ident.ns_of_lid lid  in
        FStar_List.append uu____5755 [newi]  in
      FStar_Ident.lid_of_ids uu____5754
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5777 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5777
          then
            let uu____5780 =
              let uu____5786 =
                let uu____5788 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5788  in
              let uu____5791 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5786, uu____5791)  in
            FStar_Ident.mk_ident uu____5780
          else x.FStar_Syntax_Syntax.ppname  in
        mk_field_projector_name_from_ident lid nm
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5806) -> ses
    | uu____5815 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5830 = FStar_Syntax_Unionfind.find uv  in
      match uu____5830 with
      | FStar_Pervasives_Native.Some uu____5833 ->
          let uu____5834 =
            let uu____5836 =
              let uu____5838 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5838  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5836  in
          failwith uu____5834
      | uu____5843 -> FStar_Syntax_Unionfind.change uv t
  
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
            (let uu____5867 = FStar_Ident.text_of_id l1b  in
             let uu____5869 = FStar_Ident.text_of_id l2b  in
             uu____5867 = uu____5869)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5898 = FStar_Ident.text_of_id x1  in
                      let uu____5900 = FStar_Ident.text_of_id x2  in
                      uu____5898 = uu____5900) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5909 = FStar_Ident.text_of_id x1  in
                    let uu____5911 = FStar_Ident.text_of_id x2  in
                    uu____5909 = uu____5911) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5940 = FStar_Ident.text_of_id x1  in
                      let uu____5942 = FStar_Ident.text_of_id x2  in
                      uu____5940 = uu____5942) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5951 = FStar_Ident.text_of_id x1  in
                    let uu____5953 = FStar_Ident.text_of_id x2  in
                    uu____5951 = uu____5953) f1 f2)
      | uu____5956 -> q1 = q2
  
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
              let uu____6002 =
                let uu___1000_6003 = rc  in
                let uu____6004 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1000_6003.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6004;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1000_6003.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6002
           in
        match bs with
        | [] -> t
        | uu____6021 ->
            let body =
              let uu____6023 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6023  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6053 =
                   let uu____6060 =
                     let uu____6061 =
                       let uu____6080 =
                         let uu____6089 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6089 bs'  in
                       let uu____6104 = close_lopt lopt'  in
                       (uu____6080, t1, uu____6104)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6061  in
                   FStar_Syntax_Syntax.mk uu____6060  in
                 uu____6053 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6119 ->
                 let uu____6120 =
                   let uu____6127 =
                     let uu____6128 =
                       let uu____6147 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6156 = close_lopt lopt  in
                       (uu____6147, body, uu____6156)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6128  in
                   FStar_Syntax_Syntax.mk uu____6127  in
                 uu____6120 FStar_Pervasives_Native.None
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
      | uu____6212 ->
          let uu____6221 =
            let uu____6228 =
              let uu____6229 =
                let uu____6244 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6253 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6244, uu____6253)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6229  in
            FStar_Syntax_Syntax.mk uu____6228  in
          uu____6221 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6302 =
        let uu____6303 = FStar_Syntax_Subst.compress t  in
        uu____6303.FStar_Syntax_Syntax.n  in
      match uu____6302 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6333) ->
               let uu____6342 =
                 let uu____6343 = FStar_Syntax_Subst.compress tres  in
                 uu____6343.FStar_Syntax_Syntax.n  in
               (match uu____6342 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6386 -> t)
           | uu____6387 -> t)
      | uu____6388 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6406 =
        let uu____6407 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6407 t.FStar_Syntax_Syntax.pos  in
      let uu____6408 =
        let uu____6415 =
          let uu____6416 =
            let uu____6423 =
              let uu____6426 =
                let uu____6427 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6427]  in
              FStar_Syntax_Subst.close uu____6426 t  in
            (b, uu____6423)  in
          FStar_Syntax_Syntax.Tm_refine uu____6416  in
        FStar_Syntax_Syntax.mk uu____6415  in
      uu____6408 FStar_Pervasives_Native.None uu____6406
  
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
        let uu____6507 = is_total_comp c  in
        if uu____6507
        then
          let uu____6522 = arrow_formals_comp_ln (comp_result c)  in
          (match uu____6522 with
           | (bs',k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6589;
           FStar_Syntax_Syntax.index = uu____6590;
           FStar_Syntax_Syntax.sort = s;_},uu____6592)
        ->
        let rec aux s1 k2 =
          let uu____6623 =
            let uu____6624 = FStar_Syntax_Subst.compress s1  in
            uu____6624.FStar_Syntax_Syntax.n  in
          match uu____6623 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6639 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6654;
                 FStar_Syntax_Syntax.index = uu____6655;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6657)
              -> aux s2 k2
          | uu____6665 ->
              let uu____6666 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6666)
           in
        aux s k1
    | uu____6681 ->
        let uu____6682 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6682)
  
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let uu____6707 = arrow_formals_comp_ln k  in
    match uu____6707 with | (bs,c) -> FStar_Syntax_Subst.open_comp bs c
  
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6762 = arrow_formals_comp_ln k  in
    match uu____6762 with | (bs,c) -> (bs, (comp_result c))
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6829 = arrow_formals_comp k  in
    match uu____6829 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6931 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6931 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6955 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_6964  ->
                         match uu___8_6964 with
                         | FStar_Syntax_Syntax.DECREASES uu____6966 -> true
                         | uu____6970 -> false))
                  in
               (match uu____6955 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7005 ->
                    let uu____7008 = is_total_comp c1  in
                    if uu____7008
                    then
                      let uu____7027 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7027 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7120;
             FStar_Syntax_Syntax.index = uu____7121;
             FStar_Syntax_Syntax.sort = k2;_},uu____7123)
          -> arrow_until_decreases k2
      | uu____7131 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7152 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7152 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7206 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7227 =
                 FStar_Common.tabulate n_univs (fun uu____7233  -> false)  in
               let uu____7236 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7261  ->
                         match uu____7261 with
                         | (x,uu____7270) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7227 uu____7236)
           in
        ((n_univs + (FStar_List.length bs)), uu____7206)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7326 =
            let uu___1127_7327 = rc  in
            let uu____7328 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1127_7327.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7328;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1127_7327.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7326
      | uu____7337 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7371 =
        let uu____7372 =
          let uu____7375 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7375  in
        uu____7372.FStar_Syntax_Syntax.n  in
      match uu____7371 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7421 = aux t2 what  in
          (match uu____7421 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7493 -> ([], t1, abs_body_lcomp)  in
    let uu____7510 = aux t FStar_Pervasives_Native.None  in
    match uu____7510 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7558 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7558 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let no_acc uu____7592 =
      match uu____7592 with
      | (b,aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true )) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7606 -> aq  in
          (b, aq1)
       in
    let uu____7611 = arrow_formals_comp_ln t  in
    match uu____7611 with
    | (bs,c) ->
        (match bs with
         | [] -> t
         | uu____7648 ->
             let uu____7657 =
               let uu____7664 =
                 let uu____7665 =
                   let uu____7680 = FStar_List.map no_acc bs  in
                   (uu____7680, c)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____7665  in
               FStar_Syntax_Syntax.mk uu____7664  in
             uu____7657 FStar_Pervasives_Native.None
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
                    | (FStar_Pervasives_Native.None ,uu____7851) -> def
                    | (uu____7862,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7874) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu____7890  ->
                                  FStar_Syntax_Syntax.U_name uu____7890))
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
            let uu____7972 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7972 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____8007 ->
            let t' = arrow binders c  in
            let uu____8019 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____8019 with
             | (uvs1,t'1) ->
                 let uu____8040 =
                   let uu____8041 = FStar_Syntax_Subst.compress t'1  in
                   uu____8041.FStar_Syntax_Syntax.n  in
                 (match uu____8040 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8090 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8115 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Parser_Const.is_tuple_constructor_string uu____8115
    | uu____8117 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8128 -> false
  
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
      let uu____8191 =
        let uu____8192 = pre_typ t  in uu____8192.FStar_Syntax_Syntax.n  in
      match uu____8191 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8197 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8211 =
        let uu____8212 = pre_typ t  in uu____8212.FStar_Syntax_Syntax.n  in
      match uu____8211 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8216 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8218) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8244) ->
          is_constructed_typ t1 lid
      | uu____8249 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8262 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8263 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8264 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8266) -> get_tycon t2
    | uu____8291 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8299 =
      let uu____8300 = un_uinst t  in uu____8300.FStar_Syntax_Syntax.n  in
    match uu____8299 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8305 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8319 =
        let uu____8323 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8323  in
      match uu____8319 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8355 -> false
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
  fun uu____8374  ->
    let u =
      let uu____8380 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left
        (fun uu____8397  -> FStar_Syntax_Syntax.U_unif uu____8397) uu____8380
       in
    let uu____8398 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8398, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8411 = eq_tm a a'  in
      match uu____8411 with | Equal  -> true | uu____8414 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8419 =
    let uu____8426 =
      let uu____8427 =
        let uu____8428 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8428
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8427  in
    FStar_Syntax_Syntax.mk uu____8426  in
  uu____8419 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8541 =
            let uu____8544 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8545 =
              let uu____8552 =
                let uu____8553 =
                  let uu____8570 =
                    let uu____8581 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8590 =
                      let uu____8601 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8601]  in
                    uu____8581 :: uu____8590  in
                  (tand, uu____8570)  in
                FStar_Syntax_Syntax.Tm_app uu____8553  in
              FStar_Syntax_Syntax.mk uu____8552  in
            uu____8545 FStar_Pervasives_Native.None uu____8544  in
          FStar_Pervasives_Native.Some uu____8541
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8678 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8679 =
          let uu____8686 =
            let uu____8687 =
              let uu____8704 =
                let uu____8715 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8724 =
                  let uu____8735 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8735]  in
                uu____8715 :: uu____8724  in
              (op_t, uu____8704)  in
            FStar_Syntax_Syntax.Tm_app uu____8687  in
          FStar_Syntax_Syntax.mk uu____8686  in
        uu____8679 FStar_Pervasives_Native.None uu____8678
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8792 =
      let uu____8799 =
        let uu____8800 =
          let uu____8817 =
            let uu____8828 = FStar_Syntax_Syntax.as_arg phi  in [uu____8828]
             in
          (t_not, uu____8817)  in
        FStar_Syntax_Syntax.Tm_app uu____8800  in
      FStar_Syntax_Syntax.mk uu____8799  in
    uu____8792 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____9025 =
      let uu____9032 =
        let uu____9033 =
          let uu____9050 =
            let uu____9061 = FStar_Syntax_Syntax.as_arg e  in [uu____9061]
             in
          (b2t_v, uu____9050)  in
        FStar_Syntax_Syntax.Tm_app uu____9033  in
      FStar_Syntax_Syntax.mk uu____9032  in
    uu____9025 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9108 = head_and_args e  in
    match uu____9108 with
    | (hd,args) ->
        let uu____9153 =
          let uu____9168 =
            let uu____9169 = FStar_Syntax_Subst.compress hd  in
            uu____9169.FStar_Syntax_Syntax.n  in
          (uu____9168, args)  in
        (match uu____9153 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9186)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9221 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9243 =
      let uu____9244 = unmeta t  in uu____9244.FStar_Syntax_Syntax.n  in
    match uu____9243 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9249 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9272 = is_t_true t1  in
      if uu____9272
      then t2
      else
        (let uu____9279 = is_t_true t2  in
         if uu____9279 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9307 = is_t_true t1  in
      if uu____9307
      then t_true
      else
        (let uu____9314 = is_t_true t2  in
         if uu____9314 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9343 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9344 =
        let uu____9351 =
          let uu____9352 =
            let uu____9369 =
              let uu____9380 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9389 =
                let uu____9400 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9400]  in
              uu____9380 :: uu____9389  in
            (teq, uu____9369)  in
          FStar_Syntax_Syntax.Tm_app uu____9352  in
        FStar_Syntax_Syntax.mk uu____9351  in
      uu____9344 FStar_Pervasives_Native.None uu____9343
  
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
          let uu____9467 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9468 =
            let uu____9475 =
              let uu____9476 =
                let uu____9493 =
                  let uu____9504 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9513 =
                    let uu____9524 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9533 =
                      let uu____9544 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9544]  in
                    uu____9524 :: uu____9533  in
                  uu____9504 :: uu____9513  in
                (eq_inst, uu____9493)  in
              FStar_Syntax_Syntax.Tm_app uu____9476  in
            FStar_Syntax_Syntax.mk uu____9475  in
          uu____9468 FStar_Pervasives_Native.None uu____9467
  
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
        let uu____9621 =
          let uu____9628 =
            let uu____9629 =
              let uu____9646 =
                let uu____9657 = FStar_Syntax_Syntax.iarg t  in
                let uu____9666 =
                  let uu____9677 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9686 =
                    let uu____9697 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9697]  in
                  uu____9677 :: uu____9686  in
                uu____9657 :: uu____9666  in
              (t_has_type1, uu____9646)  in
            FStar_Syntax_Syntax.Tm_app uu____9629  in
          FStar_Syntax_Syntax.mk uu____9628  in
        uu____9621 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9774 =
          let uu____9781 =
            let uu____9782 =
              let uu____9799 =
                let uu____9810 = FStar_Syntax_Syntax.iarg t  in
                let uu____9819 =
                  let uu____9830 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9830]  in
                uu____9810 :: uu____9819  in
              (t_with_type1, uu____9799)  in
            FStar_Syntax_Syntax.Tm_app uu____9782  in
          FStar_Syntax_Syntax.mk uu____9781  in
        uu____9774 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9877 =
    let uu____9884 =
      let uu____9885 =
        let uu____9892 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9892, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9885  in
    FStar_Syntax_Syntax.mk uu____9884  in
  uu____9877 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
        let uu____9975 =
          let uu____9982 =
            let uu____9983 =
              let uu____10000 =
                let uu____10011 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____10020 =
                  let uu____10031 =
                    let uu____10040 =
                      let uu____10041 =
                        let uu____10042 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10042]  in
                      abs uu____10041 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10040  in
                  [uu____10031]  in
                uu____10011 :: uu____10020  in
              (fa, uu____10000)  in
            FStar_Syntax_Syntax.Tm_app uu____9983  in
          FStar_Syntax_Syntax.mk uu____9982  in
        uu____9975 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10169 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10169
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10188 -> true
    | uu____10190 -> false
  
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
          let uu____10237 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10237, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10266 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10266, FStar_Pervasives_Native.None, t2)  in
        let uu____10280 =
          let uu____10281 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10281  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10280
  
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
      let uu____10357 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10360 =
        let uu____10371 = FStar_Syntax_Syntax.as_arg p  in [uu____10371]  in
      mk_app uu____10357 uu____10360
  
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
      let uu____10411 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10414 =
        let uu____10425 = FStar_Syntax_Syntax.as_arg p  in [uu____10425]  in
      mk_app uu____10411 uu____10414
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10460 = head_and_args t  in
    match uu____10460 with
    | (head,args) ->
        let head1 = unascribe head  in
        let head2 = un_uinst head1  in
        let uu____10509 =
          let uu____10524 =
            let uu____10525 = FStar_Syntax_Subst.compress head2  in
            uu____10525.FStar_Syntax_Syntax.n  in
          (uu____10524, args)  in
        (match uu____10509 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10544)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10610 =
                    let uu____10615 =
                      let uu____10616 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10616]  in
                    FStar_Syntax_Subst.open_term uu____10615 p  in
                  (match uu____10610 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10673 -> failwith "impossible"  in
                       let uu____10681 =
                         let uu____10683 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10683
                          in
                       if uu____10681
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10699 -> FStar_Pervasives_Native.None)
         | uu____10702 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10733 = head_and_args t  in
    match uu____10733 with
    | (head,args) ->
        let uu____10784 =
          let uu____10799 =
            let uu____10800 = FStar_Syntax_Subst.compress head  in
            uu____10800.FStar_Syntax_Syntax.n  in
          (uu____10799, args)  in
        (match uu____10784 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10822;
               FStar_Syntax_Syntax.vars = uu____10823;_},u::[]),(t1,uu____10826)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10873 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10908 = head_and_args t  in
    match uu____10908 with
    | (head,args) ->
        let uu____10959 =
          let uu____10974 =
            let uu____10975 = FStar_Syntax_Subst.compress head  in
            uu____10975.FStar_Syntax_Syntax.n  in
          (uu____10974, args)  in
        (match uu____10959 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10997;
               FStar_Syntax_Syntax.vars = uu____10998;_},u::[]),(t1,uu____11001)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11048 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11076 =
      let uu____11093 = unmeta t  in head_and_args uu____11093  in
    match uu____11076 with
    | (head,uu____11096) ->
        let uu____11121 =
          let uu____11122 = un_uinst head  in
          uu____11122.FStar_Syntax_Syntax.n  in
        (match uu____11121 with
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
         | uu____11127 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11147 =
      let uu____11148 = FStar_Syntax_Subst.compress t  in
      uu____11148.FStar_Syntax_Syntax.n  in
    match uu____11147 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11254 =
          let uu____11259 =
            let uu____11260 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11260  in
          (b, uu____11259)  in
        FStar_Pervasives_Native.Some uu____11254
    | uu____11265 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11288 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11288
      (fun uu____11316  ->
         match uu____11316 with
         | (b,c) ->
             let uu____11335 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11335 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11398 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11435 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11435
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11487 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11530 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11571 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11957) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11969) ->
          unmeta_monadic t
      | uu____11982 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12051 =
        match uu____12051 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12089  ->
                   match uu____12089 with
                   | (lid,out_lid) ->
                       let uu____12098 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12098
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12125 = head_and_args t  in
      match uu____12125 with
      | (hd,args) ->
          let uu____12170 =
            let uu____12171 = un_uinst hd  in
            uu____12171.FStar_Syntax_Syntax.n  in
          (match uu____12170 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12177 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12186 = un_squash t  in
      FStar_Util.bind_opt uu____12186
        (fun t1  ->
           let uu____12202 = head_and_args' t1  in
           match uu____12202 with
           | (hd,args) ->
               let uu____12241 =
                 let uu____12242 = un_uinst hd  in
                 uu____12242.FStar_Syntax_Syntax.n  in
               (match uu____12241 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12248 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12289,pats)) ->
          let uu____12327 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12327)
      | uu____12340 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12407 = head_and_args t1  in
        match uu____12407 with
        | (t2,args) ->
            let uu____12462 = un_uinst t2  in
            let uu____12463 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12504  ->
                      match uu____12504 with
                      | (t3,imp) ->
                          let uu____12523 = unascribe t3  in
                          (uu____12523, imp)))
               in
            (uu____12462, uu____12463)
         in
      let rec aux qopt out t1 =
        let uu____12574 = let uu____12598 = flat t1  in (qopt, uu____12598)
           in
        match uu____12574 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12638;
                 FStar_Syntax_Syntax.vars = uu____12639;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12642);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12643;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12644;_},uu____12645)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12747;
                 FStar_Syntax_Syntax.vars = uu____12748;_},uu____12749::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12752);
                  FStar_Syntax_Syntax.pos = uu____12753;
                  FStar_Syntax_Syntax.vars = uu____12754;_},uu____12755)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12872;
               FStar_Syntax_Syntax.vars = uu____12873;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12876);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12877;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12878;_},uu____12879)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12972 =
              let uu____12976 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12976  in
            aux uu____12972 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12986;
               FStar_Syntax_Syntax.vars = uu____12987;_},uu____12988::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12991);
                FStar_Syntax_Syntax.pos = uu____12992;
                FStar_Syntax_Syntax.vars = uu____12993;_},uu____12994)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13103 =
              let uu____13107 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13107  in
            aux uu____13103 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13117) ->
            let bs = FStar_List.rev out  in
            let uu____13170 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13170 with
             | (bs1,t2) ->
                 let uu____13179 = patterns t2  in
                 (match uu____13179 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13229 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13284 = un_squash t  in
      FStar_Util.bind_opt uu____13284
        (fun t1  ->
           let uu____13299 = arrow_one t1  in
           match uu____13299 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13314 =
                 let uu____13316 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13316  in
               if uu____13314
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13326 = comp_to_comp_typ_nouniv c  in
                    uu____13326.FStar_Syntax_Syntax.result_typ  in
                  let uu____13327 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13327
                  then
                    let uu____13334 = patterns q  in
                    match uu____13334 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13397 =
                       let uu____13398 =
                         let uu____13403 =
                           let uu____13404 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13415 =
                             let uu____13426 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13426]  in
                           uu____13404 :: uu____13415  in
                         (FStar_Parser_Const.imp_lid, uu____13403)  in
                       BaseConn uu____13398  in
                     FStar_Pervasives_Native.Some uu____13397))
           | uu____13459 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13467 = un_squash t  in
      FStar_Util.bind_opt uu____13467
        (fun t1  ->
           let uu____13498 = head_and_args' t1  in
           match uu____13498 with
           | (hd,args) ->
               let uu____13537 =
                 let uu____13552 =
                   let uu____13553 = un_uinst hd  in
                   uu____13553.FStar_Syntax_Syntax.n  in
                 (uu____13552, args)  in
               (match uu____13537 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13570)::(a2,uu____13572)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13623 =
                      let uu____13624 = FStar_Syntax_Subst.compress a2  in
                      uu____13624.FStar_Syntax_Syntax.n  in
                    (match uu____13623 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13631) ->
                         let uu____13666 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13666 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13719 -> failwith "impossible"  in
                              let uu____13727 = patterns q1  in
                              (match uu____13727 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13788 -> FStar_Pervasives_Native.None)
                | uu____13789 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13812 = destruct_sq_forall phi  in
          (match uu____13812 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13822  ->
                    FStar_Pervasives_Native.Some uu____13822)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13829 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13835 = destruct_sq_exists phi  in
          (match uu____13835 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13845  ->
                    FStar_Pervasives_Native.Some uu____13845)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13852 -> f1)
      | uu____13855 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13859 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13859
      (fun uu____13864  ->
         let uu____13865 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13865
           (fun uu____13870  ->
              let uu____13871 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13871
                (fun uu____13876  ->
                   let uu____13877 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13877
                     (fun uu____13882  ->
                        let uu____13883 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13883
                          (fun uu____13887  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13905 =
            let uu____13910 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13910  in
          let uu____13911 =
            let uu____13912 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13912  in
          let uu____13915 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13905 a.FStar_Syntax_Syntax.action_univs uu____13911
            FStar_Parser_Const.effect_Tot_lid uu____13915 [] pos
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
    let uu____13941 =
      let uu____13948 =
        let uu____13949 =
          let uu____13966 =
            let uu____13977 = FStar_Syntax_Syntax.as_arg t  in [uu____13977]
             in
          (reify_, uu____13966)  in
        FStar_Syntax_Syntax.Tm_app uu____13949  in
      FStar_Syntax_Syntax.mk uu____13948  in
    uu____13941 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14029 =
        let uu____14036 =
          let uu____14037 =
            let uu____14038 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14038  in
          FStar_Syntax_Syntax.Tm_constant uu____14037  in
        FStar_Syntax_Syntax.mk uu____14036  in
      uu____14029 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14040 =
      let uu____14047 =
        let uu____14048 =
          let uu____14065 =
            let uu____14076 = FStar_Syntax_Syntax.as_arg t  in [uu____14076]
             in
          (reflect_, uu____14065)  in
        FStar_Syntax_Syntax.Tm_app uu____14048  in
      FStar_Syntax_Syntax.mk uu____14047  in
    uu____14040 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14120 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14137 = unfold_lazy i  in delta_qualifier uu____14137
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14139 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14140 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14141 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14164 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14177 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14178 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14185 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14186 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14202) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14207;
           FStar_Syntax_Syntax.index = uu____14208;
           FStar_Syntax_Syntax.sort = t2;_},uu____14210)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14219) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14225,uu____14226) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14268) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14293,t2,uu____14295) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14320,t2) -> delta_qualifier t2
  
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
    let uu____14359 = delta_qualifier t  in incr_delta_depth uu____14359
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14367 =
      let uu____14368 = FStar_Syntax_Subst.compress t  in
      uu____14368.FStar_Syntax_Syntax.n  in
    match uu____14367 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14373 -> false
  
let rec apply_last :
  'uuuuuu14382 .
    ('uuuuuu14382 -> 'uuuuuu14382) ->
      'uuuuuu14382 Prims.list -> 'uuuuuu14382 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14408 = f a  in [uu____14408]
      | x::xs -> let uu____14413 = apply_last f xs  in x :: uu____14413
  
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
          let uu____14468 =
            let uu____14475 =
              let uu____14476 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14476  in
            FStar_Syntax_Syntax.mk uu____14475  in
          uu____14468 FStar_Pervasives_Native.None rng  in
        let cons args pos =
          let uu____14490 =
            let uu____14495 =
              let uu____14496 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14496
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14495 args  in
          uu____14490 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14510 =
            let uu____14515 =
              let uu____14516 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14516
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14515 args  in
          uu____14510 FStar_Pervasives_Native.None pos  in
        let uu____14517 =
          let uu____14518 =
            let uu____14519 = FStar_Syntax_Syntax.iarg typ  in [uu____14519]
             in
          nil uu____14518 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14553 =
                 let uu____14554 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14563 =
                   let uu____14574 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14583 =
                     let uu____14594 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14594]  in
                   uu____14574 :: uu____14583  in
                 uu____14554 :: uu____14563  in
               cons uu____14553 t.FStar_Syntax_Syntax.pos) l uu____14517
  
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
        | uu____14703 -> false
  
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
          | uu____14817 -> false
  
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
        | uu____14983 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15021 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15021
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
        let t11 = let uu____15225 = unmeta_safe t1  in canon_app uu____15225
           in
        let t21 = let uu____15231 = unmeta_safe t2  in canon_app uu____15231
           in
        let uu____15234 =
          let uu____15239 =
            let uu____15240 =
              let uu____15243 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15243  in
            uu____15240.FStar_Syntax_Syntax.n  in
          let uu____15244 =
            let uu____15245 =
              let uu____15248 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15248  in
            uu____15245.FStar_Syntax_Syntax.n  in
          (uu____15239, uu____15244)  in
        match uu____15234 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15250,uu____15251) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15260,FStar_Syntax_Syntax.Tm_uinst uu____15261) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15270,uu____15271) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15288,FStar_Syntax_Syntax.Tm_delayed uu____15289) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15306,uu____15307) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15336,FStar_Syntax_Syntax.Tm_ascribed uu____15337) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15376 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15376
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15381 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15381
        | (FStar_Syntax_Syntax.Tm_type
           uu____15384,FStar_Syntax_Syntax.Tm_type uu____15385) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15443 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15443) &&
              (let uu____15453 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15453)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15502 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15502) &&
              (let uu____15512 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15512)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15529 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15529) &&
              (let uu____15533 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15533)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15590 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15590) &&
              (let uu____15594 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15594)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15683 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15683) &&
              (let uu____15687 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15687)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15704,uu____15705) ->
            let uu____15706 =
              let uu____15708 = unlazy t11  in
              term_eq_dbg dbg uu____15708 t21  in
            check "lazy_l" uu____15706
        | (uu____15710,FStar_Syntax_Syntax.Tm_lazy uu____15711) ->
            let uu____15712 =
              let uu____15714 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15714  in
            check "lazy_r" uu____15712
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15759 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15759))
              &&
              (let uu____15763 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15763)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15767),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15769)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15827 =
               let uu____15829 = eq_quoteinfo qi1 qi2  in uu____15829 = Equal
                in
             check "tm_quoted qi" uu____15827) &&
              (let uu____15832 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15832)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15862 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15862) &&
                   (let uu____15866 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15866)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15885 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15885) &&
                    (let uu____15889 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15889))
                   &&
                   (let uu____15893 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15893)
             | uu____15896 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15902) -> fail "unk"
        | (uu____15904,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15906,uu____15907) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15909,uu____15910) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15912,uu____15913) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15915,uu____15916) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15918,uu____15919) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15921,uu____15922) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15942,uu____15943) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15959,uu____15960) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15968,uu____15969) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15987,uu____15988) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16012,uu____16013) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16028,uu____16029) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16043,uu____16044) ->
            fail "bottom"
        | (uu____16052,FStar_Syntax_Syntax.Tm_bvar uu____16053) ->
            fail "bottom"
        | (uu____16055,FStar_Syntax_Syntax.Tm_name uu____16056) ->
            fail "bottom"
        | (uu____16058,FStar_Syntax_Syntax.Tm_fvar uu____16059) ->
            fail "bottom"
        | (uu____16061,FStar_Syntax_Syntax.Tm_constant uu____16062) ->
            fail "bottom"
        | (uu____16064,FStar_Syntax_Syntax.Tm_type uu____16065) ->
            fail "bottom"
        | (uu____16067,FStar_Syntax_Syntax.Tm_abs uu____16068) ->
            fail "bottom"
        | (uu____16088,FStar_Syntax_Syntax.Tm_arrow uu____16089) ->
            fail "bottom"
        | (uu____16105,FStar_Syntax_Syntax.Tm_refine uu____16106) ->
            fail "bottom"
        | (uu____16114,FStar_Syntax_Syntax.Tm_app uu____16115) ->
            fail "bottom"
        | (uu____16133,FStar_Syntax_Syntax.Tm_match uu____16134) ->
            fail "bottom"
        | (uu____16158,FStar_Syntax_Syntax.Tm_let uu____16159) ->
            fail "bottom"
        | (uu____16174,FStar_Syntax_Syntax.Tm_uvar uu____16175) ->
            fail "bottom"
        | (uu____16189,FStar_Syntax_Syntax.Tm_meta uu____16190) ->
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
               let uu____16225 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16225)
          (fun q1  ->
             fun q2  ->
               let uu____16237 =
                 let uu____16239 = eq_aqual q1 q2  in uu____16239 = Equal  in
               check "arg qual" uu____16237) a1 a2

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
               let uu____16264 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16264)
          (fun q1  ->
             fun q2  ->
               let uu____16276 =
                 let uu____16278 = eq_aqual q1 q2  in uu____16278 = Equal  in
               check "binder qual" uu____16276) b1 b2

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
        ((let uu____16292 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16292) &&
           (let uu____16296 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16296))
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
    fun uu____16306  ->
      fun uu____16307  ->
        match (uu____16306, uu____16307) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16434 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16434) &&
               (let uu____16438 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16438))
              &&
              (let uu____16442 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16484 -> false  in
               check "branch when" uu____16442)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16505 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16505) &&
           (let uu____16514 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16514))
          &&
          (let uu____16518 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16518)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16535 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16535 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16589 ->
        let uu____16604 =
          let uu____16606 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16606  in
        Prims.int_one + uu____16604
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16609 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16609
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16613 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16613
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16622 = sizeof t1  in (FStar_List.length us) + uu____16622
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16626) ->
        let uu____16651 = sizeof t1  in
        let uu____16653 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16668  ->
                 match uu____16668 with
                 | (bv,uu____16678) ->
                     let uu____16683 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16683) Prims.int_zero bs
           in
        uu____16651 + uu____16653
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____16712 = sizeof hd  in
        let uu____16714 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16729  ->
                 match uu____16729 with
                 | (arg,uu____16739) ->
                     let uu____16744 = sizeof arg  in acc + uu____16744)
            Prims.int_zero args
           in
        uu____16712 + uu____16714
    | uu____16747 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16761 =
        let uu____16762 = un_uinst t  in uu____16762.FStar_Syntax_Syntax.n
         in
      match uu____16761 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16767 -> false
  
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
           let uu____16828 = head_and_args t  in
           match uu____16828 with
           | (head,args) ->
               let uu____16883 =
                 let uu____16884 = FStar_Syntax_Subst.compress head  in
                 uu____16884.FStar_Syntax_Syntax.n  in
               (match uu____16883 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16910 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____16943 = is_fvar attr a  in Prims.op_Negation uu____16943)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options s =
        let uu____16964 = FStar_Options.set_options s  in
        match uu____16964 with
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
          ((let uu____16978 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16978 (fun uu____16980  -> ()));
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
          let uu____16994 = FStar_Options.internal_pop ()  in
          if uu____16994
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
    | FStar_Syntax_Syntax.Tm_delayed uu____17026 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17045 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17060 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17061 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17062 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17071) ->
        let uu____17096 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17096 with
         | (bs1,t2) ->
             let uu____17105 =
               FStar_List.collect
                 (fun uu____17117  ->
                    match uu____17117 with
                    | (b,uu____17127) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17132 = unbound_variables t2  in
             FStar_List.append uu____17105 uu____17132)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17157 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17157 with
         | (bs1,c1) ->
             let uu____17166 =
               FStar_List.collect
                 (fun uu____17178  ->
                    match uu____17178 with
                    | (b,uu____17188) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17193 = unbound_variables_comp c1  in
             FStar_List.append uu____17166 uu____17193)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17202 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17202 with
         | (bs,t2) ->
             let uu____17225 =
               FStar_List.collect
                 (fun uu____17237  ->
                    match uu____17237 with
                    | (b1,uu____17247) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17252 = unbound_variables t2  in
             FStar_List.append uu____17225 uu____17252)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17281 =
          FStar_List.collect
            (fun uu____17295  ->
               match uu____17295 with
               | (x,uu____17307) -> unbound_variables x) args
           in
        let uu____17316 = unbound_variables t1  in
        FStar_List.append uu____17281 uu____17316
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17357 = unbound_variables t1  in
        let uu____17360 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17375 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17375 with
                  | (p,wopt,t2) ->
                      let uu____17397 = unbound_variables t2  in
                      let uu____17400 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17397 uu____17400))
           in
        FStar_List.append uu____17357 uu____17360
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17414) ->
        let uu____17455 = unbound_variables t1  in
        let uu____17458 =
          let uu____17461 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17492 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17461 uu____17492  in
        FStar_List.append uu____17455 uu____17458
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17533 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17536 =
          let uu____17539 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17542 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17547 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17549 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17549 with
                 | (uu____17570,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17539 uu____17542  in
        FStar_List.append uu____17533 uu____17536
    | FStar_Syntax_Syntax.Tm_let ((uu____17572,lbs),t1) ->
        let uu____17592 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17592 with
         | (lbs1,t2) ->
             let uu____17607 = unbound_variables t2  in
             let uu____17610 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17617 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17620 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17617 uu____17620) lbs1
                in
             FStar_List.append uu____17607 uu____17610)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17637 = unbound_variables t1  in
        let uu____17640 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17645,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17700  ->
                      match uu____17700 with
                      | (a,uu____17712) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17721,uu____17722,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17728,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17734 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17743 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17744 -> []  in
        FStar_List.append uu____17637 uu____17640

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17751) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17761) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17771 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17774 =
          FStar_List.collect
            (fun uu____17788  ->
               match uu____17788 with
               | (a,uu____17800) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17771 uu____17774

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
            let uu____17915 = head_and_args h  in
            (match uu____17915 with
             | (head,args) ->
                 let uu____17976 =
                   let uu____17977 = FStar_Syntax_Subst.compress head  in
                   uu____17977.FStar_Syntax_Syntax.n  in
                 (match uu____17976 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18030 -> aux (h :: acc) t))
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
      let uu____18054 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18054 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2482_18096 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2482_18096.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2482_18096.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2482_18096.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2482_18096.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2482_18096.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18104 =
      let uu____18105 = FStar_Syntax_Subst.compress t  in
      uu____18105.FStar_Syntax_Syntax.n  in
    match uu____18104 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18109,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18137)::uu____18138 ->
                  let pats' = unmeta pats  in
                  let uu____18198 = head_and_args pats'  in
                  (match uu____18198 with
                   | (head,uu____18217) ->
                       let uu____18242 =
                         let uu____18243 = un_uinst head  in
                         uu____18243.FStar_Syntax_Syntax.n  in
                       (match uu____18242 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18248 -> false))
              | uu____18250 -> false)
         | uu____18262 -> false)
    | uu____18264 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18280 =
      let uu____18297 = unmeta e  in head_and_args uu____18297  in
    match uu____18280 with
    | (head,args) ->
        let uu____18328 =
          let uu____18343 =
            let uu____18344 = un_uinst head  in
            uu____18344.FStar_Syntax_Syntax.n  in
          (uu____18343, args)  in
        (match uu____18328 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18362) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18386::(hd,uu____18388)::(tl,uu____18390)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18457 =
               let uu____18460 =
                 let uu____18463 = list_elements tl  in
                 FStar_Util.must uu____18463  in
               hd :: uu____18460  in
             FStar_Pervasives_Native.Some uu____18457
         | uu____18472 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18501 =
      let uu____18502 = FStar_Syntax_Subst.compress t  in
      uu____18502.FStar_Syntax_Syntax.n  in
    match uu____18501 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18509) ->
        let uu____18544 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18544 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18578 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18578
             then
               let uu____18585 =
                 let uu____18596 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18596]  in
               mk_app t uu____18585
             else e1)
    | uu____18623 ->
        let uu____18624 =
          let uu____18635 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18635]  in
        mk_app t uu____18624
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18690 = list_elements e  in
        match uu____18690 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18725 =
          let uu____18742 = unmeta p  in
          FStar_All.pipe_right uu____18742 head_and_args  in
        match uu____18725 with
        | (head,args) ->
            let uu____18793 =
              let uu____18808 =
                let uu____18809 = un_uinst head  in
                uu____18809.FStar_Syntax_Syntax.n  in
              (uu____18808, args)  in
            (match uu____18793 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18831,uu____18832)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18884 ->
                 let uu____18899 =
                   let uu____18905 =
                     let uu____18907 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18907
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____18905)  in
                 FStar_Errors.raise_error uu____18899
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____18950 =
            let uu____18967 = unmeta t1  in
            FStar_All.pipe_right uu____18967 head_and_args  in
          match uu____18950 with
          | (head,args) ->
              let uu____19014 =
                let uu____19029 =
                  let uu____19030 = un_uinst head  in
                  uu____19030.FStar_Syntax_Syntax.n  in
                (uu____19029, args)  in
              (match uu____19014 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19049)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19086 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19116 = smt_pat_or t1  in
            (match uu____19116 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19138 = list_elements1 e  in
                 FStar_All.pipe_right uu____19138
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19168 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19168
                           (FStar_List.map one_pat)))
             | uu____19197 ->
                 let uu____19202 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19202])
        | uu____19257 ->
            let uu____19260 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19260]
         in
      let uu____19315 =
        let uu____19348 =
          let uu____19349 = FStar_Syntax_Subst.compress t  in
          uu____19349.FStar_Syntax_Syntax.n  in
        match uu____19348 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19406 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19406 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19477;
                        FStar_Syntax_Syntax.effect_name = uu____19478;
                        FStar_Syntax_Syntax.result_typ = uu____19479;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19481)::(post,uu____19483)::(pats,uu____19485)::[];
                        FStar_Syntax_Syntax.flags = uu____19486;_}
                      ->
                      let uu____19547 = lemma_pats pats  in
                      (binders1, pre, post, uu____19547)
                  | uu____19584 -> failwith "impos"))
        | uu____19618 -> failwith "Impos"  in
      match uu____19315 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19710 =
              let uu____19717 =
                let uu____19718 =
                  let uu____19725 = mk_imp pre post1  in
                  let uu____19728 =
                    let uu____19729 =
                      let uu____19750 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19750, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19729  in
                  (uu____19725, uu____19728)  in
                FStar_Syntax_Syntax.Tm_meta uu____19718  in
              FStar_Syntax_Syntax.mk uu____19717  in
            uu____19710 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19774 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19774 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19804 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19815 -> true
    | uu____19817 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19828 -> true
    | uu____19830 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19848 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19849 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19850 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19851 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19852 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19853 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19854 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19855 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19858 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19861 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19848;
        FStar_Syntax_Syntax.bind_wp = uu____19849;
        FStar_Syntax_Syntax.stronger = uu____19850;
        FStar_Syntax_Syntax.if_then_else = uu____19851;
        FStar_Syntax_Syntax.ite_wp = uu____19852;
        FStar_Syntax_Syntax.close_wp = uu____19853;
        FStar_Syntax_Syntax.trivial = uu____19854;
        FStar_Syntax_Syntax.repr = uu____19855;
        FStar_Syntax_Syntax.return_repr = uu____19858;
        FStar_Syntax_Syntax.bind_repr = uu____19861
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____19893 =
        match uu____19893 with
        | (ts1,ts2) ->
            let uu____19904 = f ts1  in
            let uu____19905 = f ts2  in (uu____19904, uu____19905)
         in
      let uu____19906 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____19911 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____19916 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____19921 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____19926 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____19906;
        FStar_Syntax_Syntax.l_return = uu____19911;
        FStar_Syntax_Syntax.l_bind = uu____19916;
        FStar_Syntax_Syntax.l_subcomp = uu____19921;
        FStar_Syntax_Syntax.l_if_then_else = uu____19926
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
          let uu____19948 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____19948
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19950 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____19950
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19952 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____19952
  
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
    | uu____19967 -> FStar_Pervasives_Native.None
  
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
        let uu____19981 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19981
          (fun uu____19988  -> FStar_Pervasives_Native.Some uu____19988)
  
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
        let uu____20028 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20028
          (fun uu____20035  -> FStar_Pervasives_Native.Some uu____20035)
  
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
        let uu____20049 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20049
          (fun uu____20056  -> FStar_Pervasives_Native.Some uu____20056)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20070  -> FStar_Pervasives_Native.Some uu____20070)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20074  -> FStar_Pervasives_Native.Some uu____20074)
    | uu____20075 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20087 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20087
          (fun uu____20094  -> FStar_Pervasives_Native.Some uu____20094)
    | uu____20095 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20109  -> FStar_Pervasives_Native.Some uu____20109)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20113  -> FStar_Pervasives_Native.Some uu____20113)
    | uu____20114 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20128  -> FStar_Pervasives_Native.Some uu____20128)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20132  -> FStar_Pervasives_Native.Some uu____20132)
    | uu____20133 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20157 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20158 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20160 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20160
          (fun uu____20167  -> FStar_Pervasives_Native.Some uu____20167)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun uu____20181  -> FStar_Pervasives_Native.Some uu____20181)
    | uu____20182 -> FStar_Pervasives_Native.None
  