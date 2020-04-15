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
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5401 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5427  ->
    match uu___7_5427 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'uuuuuu5441 'uuuuuu5442 .
    ('uuuuuu5441 FStar_Syntax_Syntax.syntax * 'uuuuuu5442) ->
      FStar_Range.range
  =
  fun uu____5453  ->
    match uu____5453 with | (hd,uu____5461) -> hd.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'uuuuuu5475 'uuuuuu5476 .
    ('uuuuuu5475 FStar_Syntax_Syntax.syntax * 'uuuuuu5476) Prims.list ->
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
      | uu____5574 ->
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
      let uu____5633 =
        FStar_List.map
          (fun uu____5660  ->
             match uu____5660 with
             | (bv,aq) ->
                 let uu____5679 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5679, aq)) bs
         in
      mk_app f uu____5633
  
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
          (let uu____5730 =
             let uu____5736 =
               let uu____5738 =
                 let uu____5740 = FStar_Ident.ident_of_lid lid  in
                 FStar_Ident.text_of_id uu____5740  in
               mk_field_projector_name_from_string uu____5738 itext  in
             let uu____5741 = FStar_Ident.range_of_id i  in
             (uu____5736, uu____5741)  in
           FStar_Ident.mk_ident uu____5730)
         in
      let uu____5743 =
        let uu____5744 = FStar_Ident.ns_of_lid lid  in
        FStar_List.append uu____5744 [newi]  in
      FStar_Ident.lid_of_ids uu____5743
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5766 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5766
          then
            let uu____5769 =
              let uu____5775 =
                let uu____5777 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5777  in
              let uu____5780 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5775, uu____5780)  in
            FStar_Ident.mk_ident uu____5769
          else x.FStar_Syntax_Syntax.ppname  in
        mk_field_projector_name_from_ident lid nm
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5795) -> ses
    | uu____5804 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5819 = FStar_Syntax_Unionfind.find uv  in
      match uu____5819 with
      | FStar_Pervasives_Native.Some uu____5822 ->
          let uu____5823 =
            let uu____5825 =
              let uu____5827 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5827  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5825  in
          failwith uu____5823
      | uu____5832 -> FStar_Syntax_Unionfind.change uv t
  
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
            (let uu____5856 = FStar_Ident.text_of_id l1b  in
             let uu____5858 = FStar_Ident.text_of_id l2b  in
             uu____5856 = uu____5858)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5887 = FStar_Ident.text_of_id x1  in
                      let uu____5889 = FStar_Ident.text_of_id x2  in
                      uu____5887 = uu____5889) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5898 = FStar_Ident.text_of_id x1  in
                    let uu____5900 = FStar_Ident.text_of_id x2  in
                    uu____5898 = uu____5900) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5929 = FStar_Ident.text_of_id x1  in
                      let uu____5931 = FStar_Ident.text_of_id x2  in
                      uu____5929 = uu____5931) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5940 = FStar_Ident.text_of_id x1  in
                    let uu____5942 = FStar_Ident.text_of_id x2  in
                    uu____5940 = uu____5942) f1 f2)
      | uu____5945 -> q1 = q2
  
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
              let uu____5991 =
                let uu___1002_5992 = rc  in
                let uu____5993 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1002_5992.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____5993;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1002_5992.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____5991
           in
        match bs with
        | [] -> t
        | uu____6010 ->
            let body =
              let uu____6012 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6012  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6042 =
                   let uu____6049 =
                     let uu____6050 =
                       let uu____6069 =
                         let uu____6078 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6078 bs'  in
                       let uu____6093 = close_lopt lopt'  in
                       (uu____6069, t1, uu____6093)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6050  in
                   FStar_Syntax_Syntax.mk uu____6049  in
                 uu____6042 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6108 ->
                 let uu____6109 =
                   let uu____6116 =
                     let uu____6117 =
                       let uu____6136 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6145 = close_lopt lopt  in
                       (uu____6136, body, uu____6145)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6117  in
                   FStar_Syntax_Syntax.mk uu____6116  in
                 uu____6109 FStar_Pervasives_Native.None
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
      | uu____6201 ->
          let uu____6210 =
            let uu____6217 =
              let uu____6218 =
                let uu____6233 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6242 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6233, uu____6242)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6218  in
            FStar_Syntax_Syntax.mk uu____6217  in
          uu____6210 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6291 =
        let uu____6292 = FStar_Syntax_Subst.compress t  in
        uu____6292.FStar_Syntax_Syntax.n  in
      match uu____6291 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6322) ->
               let uu____6331 =
                 let uu____6332 = FStar_Syntax_Subst.compress tres  in
                 uu____6332.FStar_Syntax_Syntax.n  in
               (match uu____6331 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6375 -> t)
           | uu____6376 -> t)
      | uu____6377 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6395 =
        let uu____6396 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6396 t.FStar_Syntax_Syntax.pos  in
      let uu____6397 =
        let uu____6404 =
          let uu____6405 =
            let uu____6412 =
              let uu____6415 =
                let uu____6416 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6416]  in
              FStar_Syntax_Subst.close uu____6415 t  in
            (b, uu____6412)  in
          FStar_Syntax_Syntax.Tm_refine uu____6405  in
        FStar_Syntax_Syntax.mk uu____6404  in
      uu____6397 FStar_Pervasives_Native.None uu____6395
  
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
        let uu____6496 = is_total_comp c  in
        if uu____6496
        then
          let uu____6511 = arrow_formals_comp_ln (comp_result c)  in
          (match uu____6511 with
           | (bs',k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6578;
           FStar_Syntax_Syntax.index = uu____6579;
           FStar_Syntax_Syntax.sort = s;_},uu____6581)
        ->
        let rec aux s1 k2 =
          let uu____6612 =
            let uu____6613 = FStar_Syntax_Subst.compress s1  in
            uu____6613.FStar_Syntax_Syntax.n  in
          match uu____6612 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6628 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6643;
                 FStar_Syntax_Syntax.index = uu____6644;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6646)
              -> aux s2 k2
          | uu____6654 ->
              let uu____6655 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6655)
           in
        aux s k1
    | uu____6670 ->
        let uu____6671 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6671)
  
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let uu____6696 = arrow_formals_comp_ln k  in
    match uu____6696 with | (bs,c) -> FStar_Syntax_Subst.open_comp bs c
  
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6751 = arrow_formals_comp_ln k  in
    match uu____6751 with | (bs,c) -> (bs, (comp_result c))
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6818 = arrow_formals_comp k  in
    match uu____6818 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6920 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6920 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6944 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_6953  ->
                         match uu___8_6953 with
                         | FStar_Syntax_Syntax.DECREASES uu____6955 -> true
                         | uu____6959 -> false))
                  in
               (match uu____6944 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____6994 ->
                    let uu____6997 = is_total_comp c1  in
                    if uu____6997
                    then
                      let uu____7016 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7016 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7109;
             FStar_Syntax_Syntax.index = uu____7110;
             FStar_Syntax_Syntax.sort = k2;_},uu____7112)
          -> arrow_until_decreases k2
      | uu____7120 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7141 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7141 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7195 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7216 =
                 FStar_Common.tabulate n_univs (fun uu____7222  -> false)  in
               let uu____7225 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7250  ->
                         match uu____7250 with
                         | (x,uu____7259) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7216 uu____7225)
           in
        ((n_univs + (FStar_List.length bs)), uu____7195)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7315 =
            let uu___1129_7316 = rc  in
            let uu____7317 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1129_7316.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7317;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1129_7316.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7315
      | uu____7326 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7360 =
        let uu____7361 =
          let uu____7364 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7364  in
        uu____7361.FStar_Syntax_Syntax.n  in
      match uu____7360 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7410 = aux t2 what  in
          (match uu____7410 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7482 -> ([], t1, abs_body_lcomp)  in
    let uu____7499 = aux t FStar_Pervasives_Native.None  in
    match uu____7499 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7547 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7547 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let no_acc uu____7581 =
      match uu____7581 with
      | (b,aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true )) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7595 -> aq  in
          (b, aq1)
       in
    let uu____7600 = arrow_formals_comp_ln t  in
    match uu____7600 with
    | (bs,c) ->
        (match bs with
         | [] -> t
         | uu____7637 ->
             let uu____7646 =
               let uu____7653 =
                 let uu____7654 =
                   let uu____7669 = FStar_List.map no_acc bs  in
                   (uu____7669, c)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____7654  in
               FStar_Syntax_Syntax.mk uu____7653  in
             uu____7646 FStar_Pervasives_Native.None
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
                    | (FStar_Pervasives_Native.None ,uu____7840) -> def
                    | (uu____7851,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7863) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu____7879  ->
                                  FStar_Syntax_Syntax.U_name uu____7879))
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
            let uu____7961 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7961 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____7996 ->
            let t' = arrow binders c  in
            let uu____8008 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____8008 with
             | (uvs1,t'1) ->
                 let uu____8029 =
                   let uu____8030 = FStar_Syntax_Subst.compress t'1  in
                   uu____8030.FStar_Syntax_Syntax.n  in
                 (match uu____8029 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8079 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8104 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Parser_Const.is_tuple_constructor_string uu____8104
    | uu____8106 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8117 -> false
  
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
      let uu____8180 =
        let uu____8181 = pre_typ t  in uu____8181.FStar_Syntax_Syntax.n  in
      match uu____8180 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8186 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8200 =
        let uu____8201 = pre_typ t  in uu____8201.FStar_Syntax_Syntax.n  in
      match uu____8200 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8205 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8207) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8233) ->
          is_constructed_typ t1 lid
      | uu____8238 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8251 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8252 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8253 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8255) -> get_tycon t2
    | uu____8280 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8288 =
      let uu____8289 = un_uinst t  in uu____8289.FStar_Syntax_Syntax.n  in
    match uu____8288 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8294 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8308 =
        let uu____8312 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8312  in
      match uu____8308 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8344 -> false
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
  fun uu____8363  ->
    let u =
      let uu____8369 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left
        (fun uu____8386  -> FStar_Syntax_Syntax.U_unif uu____8386) uu____8369
       in
    let uu____8387 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8387, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8400 = eq_tm a a'  in
      match uu____8400 with | Equal  -> true | uu____8403 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8408 =
    let uu____8415 =
      let uu____8416 =
        let uu____8417 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8417
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8416  in
    FStar_Syntax_Syntax.mk uu____8415  in
  uu____8408 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8530 =
            let uu____8533 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8534 =
              let uu____8541 =
                let uu____8542 =
                  let uu____8559 =
                    let uu____8570 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8579 =
                      let uu____8590 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8590]  in
                    uu____8570 :: uu____8579  in
                  (tand, uu____8559)  in
                FStar_Syntax_Syntax.Tm_app uu____8542  in
              FStar_Syntax_Syntax.mk uu____8541  in
            uu____8534 FStar_Pervasives_Native.None uu____8533  in
          FStar_Pervasives_Native.Some uu____8530
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8667 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8668 =
          let uu____8675 =
            let uu____8676 =
              let uu____8693 =
                let uu____8704 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8713 =
                  let uu____8724 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8724]  in
                uu____8704 :: uu____8713  in
              (op_t, uu____8693)  in
            FStar_Syntax_Syntax.Tm_app uu____8676  in
          FStar_Syntax_Syntax.mk uu____8675  in
        uu____8668 FStar_Pervasives_Native.None uu____8667
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8781 =
      let uu____8788 =
        let uu____8789 =
          let uu____8806 =
            let uu____8817 = FStar_Syntax_Syntax.as_arg phi  in [uu____8817]
             in
          (t_not, uu____8806)  in
        FStar_Syntax_Syntax.Tm_app uu____8789  in
      FStar_Syntax_Syntax.mk uu____8788  in
    uu____8781 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____9014 =
      let uu____9021 =
        let uu____9022 =
          let uu____9039 =
            let uu____9050 = FStar_Syntax_Syntax.as_arg e  in [uu____9050]
             in
          (b2t_v, uu____9039)  in
        FStar_Syntax_Syntax.Tm_app uu____9022  in
      FStar_Syntax_Syntax.mk uu____9021  in
    uu____9014 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9097 = head_and_args e  in
    match uu____9097 with
    | (hd,args) ->
        let uu____9142 =
          let uu____9157 =
            let uu____9158 = FStar_Syntax_Subst.compress hd  in
            uu____9158.FStar_Syntax_Syntax.n  in
          (uu____9157, args)  in
        (match uu____9142 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9175)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9210 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9232 =
      let uu____9233 = unmeta t  in uu____9233.FStar_Syntax_Syntax.n  in
    match uu____9232 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9238 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9261 = is_t_true t1  in
      if uu____9261
      then t2
      else
        (let uu____9268 = is_t_true t2  in
         if uu____9268 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9296 = is_t_true t1  in
      if uu____9296
      then t_true
      else
        (let uu____9303 = is_t_true t2  in
         if uu____9303 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9332 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9333 =
        let uu____9340 =
          let uu____9341 =
            let uu____9358 =
              let uu____9369 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9378 =
                let uu____9389 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9389]  in
              uu____9369 :: uu____9378  in
            (teq, uu____9358)  in
          FStar_Syntax_Syntax.Tm_app uu____9341  in
        FStar_Syntax_Syntax.mk uu____9340  in
      uu____9333 FStar_Pervasives_Native.None uu____9332
  
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
          let uu____9456 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9457 =
            let uu____9464 =
              let uu____9465 =
                let uu____9482 =
                  let uu____9493 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9502 =
                    let uu____9513 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9522 =
                      let uu____9533 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9533]  in
                    uu____9513 :: uu____9522  in
                  uu____9493 :: uu____9502  in
                (eq_inst, uu____9482)  in
              FStar_Syntax_Syntax.Tm_app uu____9465  in
            FStar_Syntax_Syntax.mk uu____9464  in
          uu____9457 FStar_Pervasives_Native.None uu____9456
  
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
        let uu____9610 =
          let uu____9617 =
            let uu____9618 =
              let uu____9635 =
                let uu____9646 = FStar_Syntax_Syntax.iarg t  in
                let uu____9655 =
                  let uu____9666 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9675 =
                    let uu____9686 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9686]  in
                  uu____9666 :: uu____9675  in
                uu____9646 :: uu____9655  in
              (t_has_type1, uu____9635)  in
            FStar_Syntax_Syntax.Tm_app uu____9618  in
          FStar_Syntax_Syntax.mk uu____9617  in
        uu____9610 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9763 =
          let uu____9770 =
            let uu____9771 =
              let uu____9788 =
                let uu____9799 = FStar_Syntax_Syntax.iarg t  in
                let uu____9808 =
                  let uu____9819 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9819]  in
                uu____9799 :: uu____9808  in
              (t_with_type1, uu____9788)  in
            FStar_Syntax_Syntax.Tm_app uu____9771  in
          FStar_Syntax_Syntax.mk uu____9770  in
        uu____9763 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9866 =
    let uu____9873 =
      let uu____9874 =
        let uu____9881 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9881, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9874  in
    FStar_Syntax_Syntax.mk uu____9873  in
  uu____9866 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
        let uu____9964 =
          let uu____9971 =
            let uu____9972 =
              let uu____9989 =
                let uu____10000 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____10009 =
                  let uu____10020 =
                    let uu____10029 =
                      let uu____10030 =
                        let uu____10031 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10031]  in
                      abs uu____10030 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10029  in
                  [uu____10020]  in
                uu____10000 :: uu____10009  in
              (fa, uu____9989)  in
            FStar_Syntax_Syntax.Tm_app uu____9972  in
          FStar_Syntax_Syntax.mk uu____9971  in
        uu____9964 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10158 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10158
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10177 -> true
    | uu____10179 -> false
  
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
          let uu____10226 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10226, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10255 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10255, FStar_Pervasives_Native.None, t2)  in
        let uu____10269 =
          let uu____10270 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10270  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10269
  
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
      let uu____10346 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10349 =
        let uu____10360 = FStar_Syntax_Syntax.as_arg p  in [uu____10360]  in
      mk_app uu____10346 uu____10349
  
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
      let uu____10400 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10403 =
        let uu____10414 = FStar_Syntax_Syntax.as_arg p  in [uu____10414]  in
      mk_app uu____10400 uu____10403
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10449 = head_and_args t  in
    match uu____10449 with
    | (head,args) ->
        let head1 = unascribe head  in
        let head2 = un_uinst head1  in
        let uu____10498 =
          let uu____10513 =
            let uu____10514 = FStar_Syntax_Subst.compress head2  in
            uu____10514.FStar_Syntax_Syntax.n  in
          (uu____10513, args)  in
        (match uu____10498 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10533)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10599 =
                    let uu____10604 =
                      let uu____10605 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10605]  in
                    FStar_Syntax_Subst.open_term uu____10604 p  in
                  (match uu____10599 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10662 -> failwith "impossible"  in
                       let uu____10670 =
                         let uu____10672 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10672
                          in
                       if uu____10670
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10688 -> FStar_Pervasives_Native.None)
         | uu____10691 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10722 = head_and_args t  in
    match uu____10722 with
    | (head,args) ->
        let uu____10773 =
          let uu____10788 =
            let uu____10789 = FStar_Syntax_Subst.compress head  in
            uu____10789.FStar_Syntax_Syntax.n  in
          (uu____10788, args)  in
        (match uu____10773 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10811;
               FStar_Syntax_Syntax.vars = uu____10812;_},u::[]),(t1,uu____10815)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10862 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10897 = head_and_args t  in
    match uu____10897 with
    | (head,args) ->
        let uu____10948 =
          let uu____10963 =
            let uu____10964 = FStar_Syntax_Subst.compress head  in
            uu____10964.FStar_Syntax_Syntax.n  in
          (uu____10963, args)  in
        (match uu____10948 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10986;
               FStar_Syntax_Syntax.vars = uu____10987;_},u::[]),(t1,uu____10990)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11037 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11065 =
      let uu____11082 = unmeta t  in head_and_args uu____11082  in
    match uu____11065 with
    | (head,uu____11085) ->
        let uu____11110 =
          let uu____11111 = un_uinst head  in
          uu____11111.FStar_Syntax_Syntax.n  in
        (match uu____11110 with
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
         | uu____11116 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11136 =
      let uu____11137 = FStar_Syntax_Subst.compress t  in
      uu____11137.FStar_Syntax_Syntax.n  in
    match uu____11136 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11243 =
          let uu____11248 =
            let uu____11249 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11249  in
          (b, uu____11248)  in
        FStar_Pervasives_Native.Some uu____11243
    | uu____11254 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11277 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11277
      (fun uu____11305  ->
         match uu____11305 with
         | (b,c) ->
             let uu____11324 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11324 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11387 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11424 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11424
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11476 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11519 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11560 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11946) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11958) ->
          unmeta_monadic t
      | uu____11971 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12040 =
        match uu____12040 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12078  ->
                   match uu____12078 with
                   | (lid,out_lid) ->
                       let uu____12087 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12087
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12114 = head_and_args t  in
      match uu____12114 with
      | (hd,args) ->
          let uu____12159 =
            let uu____12160 = un_uinst hd  in
            uu____12160.FStar_Syntax_Syntax.n  in
          (match uu____12159 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12166 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12175 = un_squash t  in
      FStar_Util.bind_opt uu____12175
        (fun t1  ->
           let uu____12191 = head_and_args' t1  in
           match uu____12191 with
           | (hd,args) ->
               let uu____12230 =
                 let uu____12231 = un_uinst hd  in
                 uu____12231.FStar_Syntax_Syntax.n  in
               (match uu____12230 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12237 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12278,pats)) ->
          let uu____12316 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12316)
      | uu____12329 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12396 = head_and_args t1  in
        match uu____12396 with
        | (t2,args) ->
            let uu____12451 = un_uinst t2  in
            let uu____12452 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12493  ->
                      match uu____12493 with
                      | (t3,imp) ->
                          let uu____12512 = unascribe t3  in
                          (uu____12512, imp)))
               in
            (uu____12451, uu____12452)
         in
      let rec aux qopt out t1 =
        let uu____12563 = let uu____12587 = flat t1  in (qopt, uu____12587)
           in
        match uu____12563 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12627;
                 FStar_Syntax_Syntax.vars = uu____12628;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12631);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12632;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12633;_},uu____12634)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12736;
                 FStar_Syntax_Syntax.vars = uu____12737;_},uu____12738::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12741);
                  FStar_Syntax_Syntax.pos = uu____12742;
                  FStar_Syntax_Syntax.vars = uu____12743;_},uu____12744)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12861;
               FStar_Syntax_Syntax.vars = uu____12862;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12865);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12866;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12867;_},uu____12868)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12961 =
              let uu____12965 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12965  in
            aux uu____12961 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12975;
               FStar_Syntax_Syntax.vars = uu____12976;_},uu____12977::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12980);
                FStar_Syntax_Syntax.pos = uu____12981;
                FStar_Syntax_Syntax.vars = uu____12982;_},uu____12983)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13092 =
              let uu____13096 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13096  in
            aux uu____13092 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13106) ->
            let bs = FStar_List.rev out  in
            let uu____13159 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13159 with
             | (bs1,t2) ->
                 let uu____13168 = patterns t2  in
                 (match uu____13168 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13218 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13273 = un_squash t  in
      FStar_Util.bind_opt uu____13273
        (fun t1  ->
           let uu____13288 = arrow_one t1  in
           match uu____13288 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13303 =
                 let uu____13305 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13305  in
               if uu____13303
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13315 = comp_to_comp_typ_nouniv c  in
                    uu____13315.FStar_Syntax_Syntax.result_typ  in
                  let uu____13316 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13316
                  then
                    let uu____13323 = patterns q  in
                    match uu____13323 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13386 =
                       let uu____13387 =
                         let uu____13392 =
                           let uu____13393 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13404 =
                             let uu____13415 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13415]  in
                           uu____13393 :: uu____13404  in
                         (FStar_Parser_Const.imp_lid, uu____13392)  in
                       BaseConn uu____13387  in
                     FStar_Pervasives_Native.Some uu____13386))
           | uu____13448 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13456 = un_squash t  in
      FStar_Util.bind_opt uu____13456
        (fun t1  ->
           let uu____13487 = head_and_args' t1  in
           match uu____13487 with
           | (hd,args) ->
               let uu____13526 =
                 let uu____13541 =
                   let uu____13542 = un_uinst hd  in
                   uu____13542.FStar_Syntax_Syntax.n  in
                 (uu____13541, args)  in
               (match uu____13526 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13559)::(a2,uu____13561)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13612 =
                      let uu____13613 = FStar_Syntax_Subst.compress a2  in
                      uu____13613.FStar_Syntax_Syntax.n  in
                    (match uu____13612 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13620) ->
                         let uu____13655 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13655 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13708 -> failwith "impossible"  in
                              let uu____13716 = patterns q1  in
                              (match uu____13716 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13777 -> FStar_Pervasives_Native.None)
                | uu____13778 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13801 = destruct_sq_forall phi  in
          (match uu____13801 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13811  ->
                    FStar_Pervasives_Native.Some uu____13811)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13818 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13824 = destruct_sq_exists phi  in
          (match uu____13824 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13834  ->
                    FStar_Pervasives_Native.Some uu____13834)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13841 -> f1)
      | uu____13844 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13848 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13848
      (fun uu____13853  ->
         let uu____13854 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13854
           (fun uu____13859  ->
              let uu____13860 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13860
                (fun uu____13865  ->
                   let uu____13866 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13866
                     (fun uu____13871  ->
                        let uu____13872 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13872
                          (fun uu____13876  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13894 =
            let uu____13899 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13899  in
          let uu____13900 =
            let uu____13901 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13901  in
          let uu____13904 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13894 a.FStar_Syntax_Syntax.action_univs uu____13900
            FStar_Parser_Const.effect_Tot_lid uu____13904 [] pos
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
    let uu____13930 =
      let uu____13937 =
        let uu____13938 =
          let uu____13955 =
            let uu____13966 = FStar_Syntax_Syntax.as_arg t  in [uu____13966]
             in
          (reify_, uu____13955)  in
        FStar_Syntax_Syntax.Tm_app uu____13938  in
      FStar_Syntax_Syntax.mk uu____13937  in
    uu____13930 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14018 =
        let uu____14025 =
          let uu____14026 =
            let uu____14027 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14027  in
          FStar_Syntax_Syntax.Tm_constant uu____14026  in
        FStar_Syntax_Syntax.mk uu____14025  in
      uu____14018 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14029 =
      let uu____14036 =
        let uu____14037 =
          let uu____14054 =
            let uu____14065 = FStar_Syntax_Syntax.as_arg t  in [uu____14065]
             in
          (reflect_, uu____14054)  in
        FStar_Syntax_Syntax.Tm_app uu____14037  in
      FStar_Syntax_Syntax.mk uu____14036  in
    uu____14029 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14109 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14126 = unfold_lazy i  in delta_qualifier uu____14126
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14128 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14129 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14130 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14153 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14166 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14167 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14174 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14175 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14191) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14196;
           FStar_Syntax_Syntax.index = uu____14197;
           FStar_Syntax_Syntax.sort = t2;_},uu____14199)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14208) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14214,uu____14215) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14257) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14282,t2,uu____14284) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14309,t2) -> delta_qualifier t2
  
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
    let uu____14348 = delta_qualifier t  in incr_delta_depth uu____14348
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14356 =
      let uu____14357 = FStar_Syntax_Subst.compress t  in
      uu____14357.FStar_Syntax_Syntax.n  in
    match uu____14356 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14362 -> false
  
let rec apply_last :
  'uuuuuu14371 .
    ('uuuuuu14371 -> 'uuuuuu14371) ->
      'uuuuuu14371 Prims.list -> 'uuuuuu14371 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14397 = f a  in [uu____14397]
      | x::xs -> let uu____14402 = apply_last f xs  in x :: uu____14402
  
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
          let uu____14457 =
            let uu____14464 =
              let uu____14465 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14465  in
            FStar_Syntax_Syntax.mk uu____14464  in
          uu____14457 FStar_Pervasives_Native.None rng  in
        let cons args pos =
          let uu____14479 =
            let uu____14484 =
              let uu____14485 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14485
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14484 args  in
          uu____14479 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14499 =
            let uu____14504 =
              let uu____14505 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14505
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14504 args  in
          uu____14499 FStar_Pervasives_Native.None pos  in
        let uu____14506 =
          let uu____14507 =
            let uu____14508 = FStar_Syntax_Syntax.iarg typ  in [uu____14508]
             in
          nil uu____14507 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14542 =
                 let uu____14543 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14552 =
                   let uu____14563 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14572 =
                     let uu____14583 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14583]  in
                   uu____14563 :: uu____14572  in
                 uu____14543 :: uu____14552  in
               cons uu____14542 t.FStar_Syntax_Syntax.pos) l uu____14506
  
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
        | uu____14692 -> false
  
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
          | uu____14806 -> false
  
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
        | uu____14972 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15010 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15010
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
        let t11 = let uu____15214 = unmeta_safe t1  in canon_app uu____15214
           in
        let t21 = let uu____15220 = unmeta_safe t2  in canon_app uu____15220
           in
        let uu____15223 =
          let uu____15228 =
            let uu____15229 =
              let uu____15232 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15232  in
            uu____15229.FStar_Syntax_Syntax.n  in
          let uu____15233 =
            let uu____15234 =
              let uu____15237 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15237  in
            uu____15234.FStar_Syntax_Syntax.n  in
          (uu____15228, uu____15233)  in
        match uu____15223 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15239,uu____15240) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15249,FStar_Syntax_Syntax.Tm_uinst uu____15250) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15259,uu____15260) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15277,FStar_Syntax_Syntax.Tm_delayed uu____15278) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15295,uu____15296) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15325,FStar_Syntax_Syntax.Tm_ascribed uu____15326) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15365 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15365
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15370 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15370
        | (FStar_Syntax_Syntax.Tm_type
           uu____15373,FStar_Syntax_Syntax.Tm_type uu____15374) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15432 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15432) &&
              (let uu____15442 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15442)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15491 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15491) &&
              (let uu____15501 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15501)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15518 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15518) &&
              (let uu____15522 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15522)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15579 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15579) &&
              (let uu____15583 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15583)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15672 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15672) &&
              (let uu____15676 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15676)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15693,uu____15694) ->
            let uu____15695 =
              let uu____15697 = unlazy t11  in
              term_eq_dbg dbg uu____15697 t21  in
            check "lazy_l" uu____15695
        | (uu____15699,FStar_Syntax_Syntax.Tm_lazy uu____15700) ->
            let uu____15701 =
              let uu____15703 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15703  in
            check "lazy_r" uu____15701
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15748 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15748))
              &&
              (let uu____15752 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15752)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15756),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15758)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15816 =
               let uu____15818 = eq_quoteinfo qi1 qi2  in uu____15818 = Equal
                in
             check "tm_quoted qi" uu____15816) &&
              (let uu____15821 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15821)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15851 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15851) &&
                   (let uu____15855 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15855)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15874 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15874) &&
                    (let uu____15878 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15878))
                   &&
                   (let uu____15882 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15882)
             | uu____15885 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15891) -> fail "unk"
        | (uu____15893,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15895,uu____15896) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15898,uu____15899) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15901,uu____15902) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15904,uu____15905) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15907,uu____15908) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15910,uu____15911) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15931,uu____15932) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15948,uu____15949) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15957,uu____15958) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15976,uu____15977) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16001,uu____16002) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16017,uu____16018) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16032,uu____16033) ->
            fail "bottom"
        | (uu____16041,FStar_Syntax_Syntax.Tm_bvar uu____16042) ->
            fail "bottom"
        | (uu____16044,FStar_Syntax_Syntax.Tm_name uu____16045) ->
            fail "bottom"
        | (uu____16047,FStar_Syntax_Syntax.Tm_fvar uu____16048) ->
            fail "bottom"
        | (uu____16050,FStar_Syntax_Syntax.Tm_constant uu____16051) ->
            fail "bottom"
        | (uu____16053,FStar_Syntax_Syntax.Tm_type uu____16054) ->
            fail "bottom"
        | (uu____16056,FStar_Syntax_Syntax.Tm_abs uu____16057) ->
            fail "bottom"
        | (uu____16077,FStar_Syntax_Syntax.Tm_arrow uu____16078) ->
            fail "bottom"
        | (uu____16094,FStar_Syntax_Syntax.Tm_refine uu____16095) ->
            fail "bottom"
        | (uu____16103,FStar_Syntax_Syntax.Tm_app uu____16104) ->
            fail "bottom"
        | (uu____16122,FStar_Syntax_Syntax.Tm_match uu____16123) ->
            fail "bottom"
        | (uu____16147,FStar_Syntax_Syntax.Tm_let uu____16148) ->
            fail "bottom"
        | (uu____16163,FStar_Syntax_Syntax.Tm_uvar uu____16164) ->
            fail "bottom"
        | (uu____16178,FStar_Syntax_Syntax.Tm_meta uu____16179) ->
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
               let uu____16214 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16214)
          (fun q1  ->
             fun q2  ->
               let uu____16226 =
                 let uu____16228 = eq_aqual q1 q2  in uu____16228 = Equal  in
               check "arg qual" uu____16226) a1 a2

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
               let uu____16253 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16253)
          (fun q1  ->
             fun q2  ->
               let uu____16265 =
                 let uu____16267 = eq_aqual q1 q2  in uu____16267 = Equal  in
               check "binder qual" uu____16265) b1 b2

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
        ((let uu____16281 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16281) &&
           (let uu____16285 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16285))
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
    fun uu____16295  ->
      fun uu____16296  ->
        match (uu____16295, uu____16296) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16423 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16423) &&
               (let uu____16427 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16427))
              &&
              (let uu____16431 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16473 -> false  in
               check "branch when" uu____16431)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16494 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16494) &&
           (let uu____16503 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16503))
          &&
          (let uu____16507 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16507)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16524 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16524 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16578 ->
        let uu____16593 =
          let uu____16595 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16595  in
        Prims.int_one + uu____16593
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16598 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16598
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16602 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16602
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16611 = sizeof t1  in (FStar_List.length us) + uu____16611
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16615) ->
        let uu____16640 = sizeof t1  in
        let uu____16642 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16657  ->
                 match uu____16657 with
                 | (bv,uu____16667) ->
                     let uu____16672 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16672) Prims.int_zero bs
           in
        uu____16640 + uu____16642
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____16701 = sizeof hd  in
        let uu____16703 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16718  ->
                 match uu____16718 with
                 | (arg,uu____16728) ->
                     let uu____16733 = sizeof arg  in acc + uu____16733)
            Prims.int_zero args
           in
        uu____16701 + uu____16703
    | uu____16736 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16750 =
        let uu____16751 = un_uinst t  in uu____16751.FStar_Syntax_Syntax.n
         in
      match uu____16750 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16756 -> false
  
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
           let uu____16817 = head_and_args t  in
           match uu____16817 with
           | (head,args) ->
               let uu____16872 =
                 let uu____16873 = FStar_Syntax_Subst.compress head  in
                 uu____16873.FStar_Syntax_Syntax.n  in
               (match uu____16872 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16899 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____16932 = is_fvar attr a  in Prims.op_Negation uu____16932)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options s =
        let uu____16953 = FStar_Options.set_options s  in
        match uu____16953 with
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
          ((let uu____16967 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____16967 (fun uu____16969  -> ()));
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
          let uu____16983 = FStar_Options.internal_pop ()  in
          if uu____16983
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
    | FStar_Syntax_Syntax.Tm_delayed uu____17015 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17034 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17049 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17050 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17051 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17060) ->
        let uu____17085 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17085 with
         | (bs1,t2) ->
             let uu____17094 =
               FStar_List.collect
                 (fun uu____17106  ->
                    match uu____17106 with
                    | (b,uu____17116) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17121 = unbound_variables t2  in
             FStar_List.append uu____17094 uu____17121)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17146 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17146 with
         | (bs1,c1) ->
             let uu____17155 =
               FStar_List.collect
                 (fun uu____17167  ->
                    match uu____17167 with
                    | (b,uu____17177) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17182 = unbound_variables_comp c1  in
             FStar_List.append uu____17155 uu____17182)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17191 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17191 with
         | (bs,t2) ->
             let uu____17214 =
               FStar_List.collect
                 (fun uu____17226  ->
                    match uu____17226 with
                    | (b1,uu____17236) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17241 = unbound_variables t2  in
             FStar_List.append uu____17214 uu____17241)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17270 =
          FStar_List.collect
            (fun uu____17284  ->
               match uu____17284 with
               | (x,uu____17296) -> unbound_variables x) args
           in
        let uu____17305 = unbound_variables t1  in
        FStar_List.append uu____17270 uu____17305
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17346 = unbound_variables t1  in
        let uu____17349 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17364 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17364 with
                  | (p,wopt,t2) ->
                      let uu____17386 = unbound_variables t2  in
                      let uu____17389 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17386 uu____17389))
           in
        FStar_List.append uu____17346 uu____17349
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17403) ->
        let uu____17444 = unbound_variables t1  in
        let uu____17447 =
          let uu____17450 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17481 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17450 uu____17481  in
        FStar_List.append uu____17444 uu____17447
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17522 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17525 =
          let uu____17528 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17531 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17536 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17538 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17538 with
                 | (uu____17559,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17528 uu____17531  in
        FStar_List.append uu____17522 uu____17525
    | FStar_Syntax_Syntax.Tm_let ((uu____17561,lbs),t1) ->
        let uu____17581 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17581 with
         | (lbs1,t2) ->
             let uu____17596 = unbound_variables t2  in
             let uu____17599 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17606 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17609 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17606 uu____17609) lbs1
                in
             FStar_List.append uu____17596 uu____17599)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17626 = unbound_variables t1  in
        let uu____17629 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17634,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17689  ->
                      match uu____17689 with
                      | (a,uu____17701) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17710,uu____17711,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17717,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17723 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17732 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17733 -> []  in
        FStar_List.append uu____17626 uu____17629

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17740) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17750) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17760 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17763 =
          FStar_List.collect
            (fun uu____17777  ->
               match uu____17777 with
               | (a,uu____17789) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17760 uu____17763

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
            let uu____17904 = head_and_args h  in
            (match uu____17904 with
             | (head,args) ->
                 let uu____17965 =
                   let uu____17966 = FStar_Syntax_Subst.compress head  in
                   uu____17966.FStar_Syntax_Syntax.n  in
                 (match uu____17965 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18019 -> aux (h :: acc) t))
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
      let uu____18043 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18043 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2484_18085 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2484_18085.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2484_18085.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2484_18085.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2484_18085.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2484_18085.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18093 =
      let uu____18094 = FStar_Syntax_Subst.compress t  in
      uu____18094.FStar_Syntax_Syntax.n  in
    match uu____18093 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18098,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18126)::uu____18127 ->
                  let pats' = unmeta pats  in
                  let uu____18187 = head_and_args pats'  in
                  (match uu____18187 with
                   | (head,uu____18206) ->
                       let uu____18231 =
                         let uu____18232 = un_uinst head  in
                         uu____18232.FStar_Syntax_Syntax.n  in
                       (match uu____18231 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18237 -> false))
              | uu____18239 -> false)
         | uu____18251 -> false)
    | uu____18253 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18269 =
      let uu____18286 = unmeta e  in head_and_args uu____18286  in
    match uu____18269 with
    | (head,args) ->
        let uu____18317 =
          let uu____18332 =
            let uu____18333 = un_uinst head  in
            uu____18333.FStar_Syntax_Syntax.n  in
          (uu____18332, args)  in
        (match uu____18317 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18351) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18375::(hd,uu____18377)::(tl,uu____18379)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18446 =
               let uu____18449 =
                 let uu____18452 = list_elements tl  in
                 FStar_Util.must uu____18452  in
               hd :: uu____18449  in
             FStar_Pervasives_Native.Some uu____18446
         | uu____18461 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18490 =
      let uu____18491 = FStar_Syntax_Subst.compress t  in
      uu____18491.FStar_Syntax_Syntax.n  in
    match uu____18490 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18498) ->
        let uu____18533 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18533 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18567 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18567
             then
               let uu____18574 =
                 let uu____18585 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18585]  in
               mk_app t uu____18574
             else e1)
    | uu____18612 ->
        let uu____18613 =
          let uu____18624 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18624]  in
        mk_app t uu____18613
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18679 = list_elements e  in
        match uu____18679 with
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
        | (head,args) ->
            let uu____18782 =
              let uu____18797 =
                let uu____18798 = un_uinst head  in
                uu____18798.FStar_Syntax_Syntax.n  in
              (uu____18797, args)  in
            (match uu____18782 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18820,uu____18821)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18873 ->
                 let uu____18888 =
                   let uu____18894 =
                     let uu____18896 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18896
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____18894)  in
                 FStar_Errors.raise_error uu____18888
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____18939 =
            let uu____18956 = unmeta t1  in
            FStar_All.pipe_right uu____18956 head_and_args  in
          match uu____18939 with
          | (head,args) ->
              let uu____19003 =
                let uu____19018 =
                  let uu____19019 = un_uinst head  in
                  uu____19019.FStar_Syntax_Syntax.n  in
                (uu____19018, args)  in
              (match uu____19003 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19038)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19075 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19105 = smt_pat_or t1  in
            (match uu____19105 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19127 = list_elements1 e  in
                 FStar_All.pipe_right uu____19127
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19157 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19157
                           (FStar_List.map one_pat)))
             | uu____19186 ->
                 let uu____19191 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19191])
        | uu____19246 ->
            let uu____19249 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19249]
         in
      let uu____19304 =
        let uu____19337 =
          let uu____19338 = FStar_Syntax_Subst.compress t  in
          uu____19338.FStar_Syntax_Syntax.n  in
        match uu____19337 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19395 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19395 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19466;
                        FStar_Syntax_Syntax.effect_name = uu____19467;
                        FStar_Syntax_Syntax.result_typ = uu____19468;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19470)::(post,uu____19472)::(pats,uu____19474)::[];
                        FStar_Syntax_Syntax.flags = uu____19475;_}
                      ->
                      let uu____19536 = lemma_pats pats  in
                      (binders1, pre, post, uu____19536)
                  | uu____19573 -> failwith "impos"))
        | uu____19607 -> failwith "Impos"  in
      match uu____19304 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19699 =
              let uu____19706 =
                let uu____19707 =
                  let uu____19714 = mk_imp pre post1  in
                  let uu____19717 =
                    let uu____19718 =
                      let uu____19739 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19739, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19718  in
                  (uu____19714, uu____19717)  in
                FStar_Syntax_Syntax.Tm_meta uu____19707  in
              FStar_Syntax_Syntax.mk uu____19706  in
            uu____19699 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19763 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19763 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19793 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19804 -> true
    | uu____19806 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19817 -> true
    | uu____19819 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19837 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19838 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19839 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19840 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19841 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19842 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19843 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19844 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19847 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19850 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19837;
        FStar_Syntax_Syntax.bind_wp = uu____19838;
        FStar_Syntax_Syntax.stronger = uu____19839;
        FStar_Syntax_Syntax.if_then_else = uu____19840;
        FStar_Syntax_Syntax.ite_wp = uu____19841;
        FStar_Syntax_Syntax.close_wp = uu____19842;
        FStar_Syntax_Syntax.trivial = uu____19843;
        FStar_Syntax_Syntax.repr = uu____19844;
        FStar_Syntax_Syntax.return_repr = uu____19847;
        FStar_Syntax_Syntax.bind_repr = uu____19850
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____19882 =
        match uu____19882 with
        | (ts1,ts2) ->
            let uu____19893 = f ts1  in
            let uu____19894 = f ts2  in (uu____19893, uu____19894)
         in
      let uu____19895 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____19900 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____19905 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____19910 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____19915 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____19895;
        FStar_Syntax_Syntax.l_return = uu____19900;
        FStar_Syntax_Syntax.l_bind = uu____19905;
        FStar_Syntax_Syntax.l_subcomp = uu____19910;
        FStar_Syntax_Syntax.l_if_then_else = uu____19915
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
          let uu____19937 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____19937
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19939 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____19939
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19941 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____19941
  
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
    | uu____19956 -> FStar_Pervasives_Native.None
  
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
        let uu____19970 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19970
          (fun uu____19977  -> FStar_Pervasives_Native.Some uu____19977)
  
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
        let uu____20017 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20017
          (fun uu____20024  -> FStar_Pervasives_Native.Some uu____20024)
  
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
        let uu____20038 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20038
          (fun uu____20045  -> FStar_Pervasives_Native.Some uu____20045)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20059  -> FStar_Pervasives_Native.Some uu____20059)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20063  -> FStar_Pervasives_Native.Some uu____20063)
    | uu____20064 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20076 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20076
          (fun uu____20083  -> FStar_Pervasives_Native.Some uu____20083)
    | uu____20084 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20098  -> FStar_Pervasives_Native.Some uu____20098)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20102  -> FStar_Pervasives_Native.Some uu____20102)
    | uu____20103 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20117  -> FStar_Pervasives_Native.Some uu____20117)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20121  -> FStar_Pervasives_Native.Some uu____20121)
    | uu____20122 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20146 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20147 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20149 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20149
          (fun uu____20156  -> FStar_Pervasives_Native.Some uu____20156)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun uu____20170  -> FStar_Pervasives_Native.Some uu____20170)
    | uu____20171 -> FStar_Pervasives_Native.None
  