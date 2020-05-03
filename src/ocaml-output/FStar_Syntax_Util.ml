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
  
let (unmeta_lift : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1117 =
      let uu____1118 = FStar_Syntax_Subst.compress t  in
      uu____1118.FStar_Syntax_Syntax.n  in
    match uu____1117 with
    | FStar_Syntax_Syntax.Tm_meta
        (t1,FStar_Syntax_Syntax.Meta_monadic_lift uu____1122) -> t1
    | uu____1135 -> t
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_name uu____1154 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_unif uu____1157 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_max uu____1170 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_zero  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1178 = univ_kernel u1  in
        (match uu____1178 with | (k,n) -> (k, (n + Prims.int_one)))
    | FStar_Syntax_Syntax.U_bvar uu____1195 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____1210 = univ_kernel u  in FStar_Pervasives_Native.snd uu____1210
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      let rec compare_kernel uk1 uk2 =
        match (uk1, uk2) with
        | (FStar_Syntax_Syntax.U_bvar uu____1243,uu____1244) ->
            failwith "Impossible: compare_kernel bvar"
        | (uu____1248,FStar_Syntax_Syntax.U_bvar uu____1249) ->
            failwith "Impossible: compare_kernel bvar"
        | (FStar_Syntax_Syntax.U_succ uu____1253,uu____1254) ->
            failwith "Impossible: compare_kernel succ"
        | (uu____1257,FStar_Syntax_Syntax.U_succ uu____1258) ->
            failwith "Impossible: compare_kernel succ"
        | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_unknown ,uu____1262) -> ~- Prims.int_one
        | (uu____1264,FStar_Syntax_Syntax.U_unknown ) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_zero ,uu____1267) -> ~- Prims.int_one
        | (uu____1269,FStar_Syntax_Syntax.U_zero ) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
            let uu____1273 = FStar_Ident.text_of_id u11  in
            let uu____1275 = FStar_Ident.text_of_id u21  in
            FStar_String.compare uu____1273 uu____1275
        | (FStar_Syntax_Syntax.U_name uu____1277,uu____1278) ->
            ~- Prims.int_one
        | (uu____1280,FStar_Syntax_Syntax.U_name uu____1281) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
            let uu____1305 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
            let uu____1307 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
            uu____1305 - uu____1307
        | (FStar_Syntax_Syntax.U_unif uu____1309,uu____1310) ->
            ~- Prims.int_one
        | (uu____1322,FStar_Syntax_Syntax.U_unif uu____1323) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
            let n1 = FStar_List.length us1  in
            let n2 = FStar_List.length us2  in
            if n1 <> n2
            then n1 - n2
            else
              (let copt =
                 let uu____1351 = FStar_List.zip us1 us2  in
                 FStar_Util.find_map uu____1351
                   (fun uu____1367  ->
                      match uu____1367 with
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
      let uu____1395 = univ_kernel u1  in
      match uu____1395 with
      | (uk1,n1) ->
          let uu____1406 = univ_kernel u2  in
          (match uu____1406 with
           | (uk2,n2) ->
               let uu____1417 = compare_kernel uk1 uk2  in
               (match uu____1417 with
                | uu____1420 when uu____1420 = Prims.int_zero -> n1 - n2
                | n -> n))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1435 = compare_univs u1 u2  in uu____1435 = Prims.int_zero
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1454 =
        let uu____1455 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1455;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1454
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1475 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1484 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1507 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1516 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1543 =
          let uu____1544 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1544  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1543;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1573 =
          let uu____1574 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1574  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1573;
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
      let uu___239_1610 = c  in
      let uu____1611 =
        let uu____1612 =
          let uu___241_1613 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___241_1613.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___241_1613.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___241_1613.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___241_1613.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1612  in
      {
        FStar_Syntax_Syntax.n = uu____1611;
        FStar_Syntax_Syntax.pos = (uu___239_1610.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___239_1610.FStar_Syntax_Syntax.vars)
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
    | uu____1653 ->
        failwith "Assertion failed: Computation type without universe"
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1675)::[] -> wp
      | uu____1700 ->
          let uu____1711 =
            let uu____1713 =
              FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name  in
            let uu____1715 =
              let uu____1717 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length
                 in
              FStar_All.pipe_right uu____1717 FStar_Util.string_of_int  in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args"
              uu____1713 uu____1715
             in
          failwith uu____1711
       in
    let uu____1741 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1741, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1755 -> true
    | FStar_Syntax_Syntax.GTotal uu____1765 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1790  ->
               match uu___0_1790 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1794 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1811  ->
            match uu___1_1811 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1815 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1847 -> true
    | FStar_Syntax_Syntax.GTotal uu____1857 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_1872  ->
                   match uu___2_1872 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1875 -> false)))
  
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
    let uu____1916 =
      let uu____1917 = FStar_Syntax_Subst.compress t  in
      uu____1917.FStar_Syntax_Syntax.n  in
    match uu____1916 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1921,c) -> is_pure_or_ghost_comp c
    | uu____1943 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1958 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1967 =
      let uu____1968 = FStar_Syntax_Subst.compress t  in
      uu____1968.FStar_Syntax_Syntax.n  in
    match uu____1967 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1972,c) -> is_lemma_comp c
    | uu____1994 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2002 =
      let uu____2003 = FStar_Syntax_Subst.compress t  in
      uu____2003.FStar_Syntax_Syntax.n  in
    match uu____2002 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____2007) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____2033) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2070,t1,uu____2072) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2098,uu____2099) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2141) -> head_of t1
    | uu____2146 -> t
  
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
    | uu____2224 -> (t1, [])
  
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
        let uu____2306 = head_and_args' head  in
        (match uu____2306 with
         | (head1,args') -> (head1, (FStar_List.append args' args)))
    | uu____2375 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2402) ->
        FStar_Syntax_Subst.compress t2
    | uu____2407 -> t1
  
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
                (fun uu___3_2425  ->
                   match uu___3_2425 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2428 -> false)))
    | uu____2430 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2447) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2457) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2486 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2495 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___380_2507 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___380_2507.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___380_2507.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___380_2507.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___380_2507.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2523  ->
            match uu___4_2523 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2527 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2535 -> []
    | FStar_Syntax_Syntax.GTotal uu____2552 -> []
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
    | uu____2596 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2606,uu____2607) ->
        unascribe e2
    | uu____2648 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2701,uu____2702) ->
          ascribe t' k
      | uu____2743 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2770 =
      let uu____2779 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2779  in
    uu____2770 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2835 =
      let uu____2836 = FStar_Syntax_Subst.compress t  in
      uu____2836.FStar_Syntax_Syntax.n  in
    match uu____2835 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2840 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2840
    | uu____2841 -> t
  
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2848 =
      let uu____2849 = FStar_Syntax_Subst.compress t  in
      uu____2849.FStar_Syntax_Syntax.n  in
    match uu____2848 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2853 ->
             let uu____2862 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____2862
         | uu____2863 -> t)
    | uu____2864 -> t
  
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
      | uu____2889 -> false
  
let unlazy_as_t :
  'uuuuuu2902 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'uuuuuu2902
  =
  fun k  ->
    fun t  ->
      let uu____2913 =
        let uu____2914 = FStar_Syntax_Subst.compress t  in
        uu____2914.FStar_Syntax_Syntax.n  in
      match uu____2913 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2919;
            FStar_Syntax_Syntax.rng = uu____2920;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____2923 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2964 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2964;
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
    let uu____2977 =
      let uu____2992 = unascribe t  in head_and_args' uu____2992  in
    match uu____2977 with
    | (hd,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____3026 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____3037 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____3048 -> false
  
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
      | (NotEqual ,uu____3098) -> NotEqual
      | (uu____3099,NotEqual ) -> NotEqual
      | (Unknown ,uu____3100) -> Unknown
      | (uu____3101,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___5_3210 = if uu___5_3210 then Equal else Unknown  in
      let equal_iff uu___6_3221 = if uu___6_3221 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____3242 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3264 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3264
        then
          let uu____3268 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3345  ->
                    match uu____3345 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3386 = eq_tm a1 a2  in
                        eq_inj acc uu____3386) Equal) uu____3268
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3400 =
          let uu____3417 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3417 head_and_args  in
        match uu____3400 with
        | (head1,args1) ->
            let uu____3470 =
              let uu____3487 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3487 head_and_args  in
            (match uu____3470 with
             | (head2,args2) ->
                 let uu____3540 =
                   let uu____3545 =
                     let uu____3546 = un_uinst head1  in
                     uu____3546.FStar_Syntax_Syntax.n  in
                   let uu____3549 =
                     let uu____3550 = un_uinst head2  in
                     uu____3550.FStar_Syntax_Syntax.n  in
                   (uu____3545, uu____3549)  in
                 (match uu____3540 with
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
                  | uu____3577 -> FStar_Pervasives_Native.None))
         in
      let t12 = unmeta t11  in
      let t22 = unmeta t21  in
      match ((t12.FStar_Syntax_Syntax.n), (t22.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3595,uu____3596) ->
          let uu____3597 = unlazy t12  in eq_tm uu____3597 t22
      | (uu____3598,FStar_Syntax_Syntax.Tm_lazy uu____3599) ->
          let uu____3600 = unlazy t22  in eq_tm t12 uu____3600
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          let uu____3603 = FStar_Syntax_Syntax.bv_eq a b  in
          equal_if uu____3603
      | uu____3605 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3629 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3629
            (fun uu____3677  ->
               match uu____3677 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3692 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3692
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3706 = eq_tm f g  in
          eq_and uu____3706
            (fun uu____3709  ->
               let uu____3710 = eq_univs_list us vs  in equal_if uu____3710)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3712),uu____3713) -> Unknown
      | (uu____3714,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3715)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3718 = FStar_Const.eq_const c d  in equal_iff uu____3718
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3721)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3723))) ->
          let uu____3752 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3752
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3806 =
            let uu____3811 =
              let uu____3812 = un_uinst h1  in
              uu____3812.FStar_Syntax_Syntax.n  in
            let uu____3815 =
              let uu____3816 = un_uinst h2  in
              uu____3816.FStar_Syntax_Syntax.n  in
            (uu____3811, uu____3815)  in
          (match uu____3806 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3822 =
                    let uu____3824 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3824  in
                  FStar_List.mem uu____3822 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3826 ->
               let uu____3831 = eq_tm h1 h2  in
               eq_and uu____3831 (fun uu____3833  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t13,bs1),FStar_Syntax_Syntax.Tm_match
         (t23,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3939 = FStar_List.zip bs1 bs2  in
            let uu____4002 = eq_tm t13 t23  in
            FStar_List.fold_right
              (fun uu____4039  ->
                 fun a  ->
                   match uu____4039 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4132  -> branch_matches b1 b2))
              uu____3939 uu____4002
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v) ->
          let uu____4137 = eq_univs u v  in equal_if uu____4137
      | (FStar_Syntax_Syntax.Tm_quoted (t13,q1),FStar_Syntax_Syntax.Tm_quoted
         (t23,q2)) ->
          let uu____4151 = eq_quoteinfo q1 q2  in
          eq_and uu____4151 (fun uu____4153  -> eq_tm t13 t23)
      | (FStar_Syntax_Syntax.Tm_refine
         (t13,phi1),FStar_Syntax_Syntax.Tm_refine (t23,phi2)) ->
          let uu____4166 =
            eq_tm t13.FStar_Syntax_Syntax.sort t23.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4166 (fun uu____4168  -> eq_tm phi1 phi2)
      | uu____4169 -> Unknown

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
      | ([],uu____4241) -> NotEqual
      | (uu____4272,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          let uu____4361 =
            let uu____4363 = FStar_Syntax_Syntax.bv_eq x1 x2  in
            Prims.op_Negation uu____4363  in
          if uu____4361
          then NotEqual
          else
            (let uu____4368 = eq_tm t1 t2  in
             match uu____4368 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4369 = eq_antiquotes a11 a21  in
                 (match uu____4369 with
                  | NotEqual  -> NotEqual
                  | uu____4370 -> Unknown)
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
        | (uu____4454,uu____4455) -> false  in
      let uu____4465 = b1  in
      match uu____4465 with
      | (p1,w1,t1) ->
          let uu____4499 = b2  in
          (match uu____4499 with
           | (p2,w2,t2) ->
               let uu____4533 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4533
               then
                 let uu____4536 =
                   (let uu____4540 = eq_tm t1 t2  in uu____4540 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4549 = eq_tm t11 t21  in
                             uu____4549 = Equal) w1 w2)
                    in
                 (if uu____4536 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4614)::a11,(b,uu____4617)::b1) ->
          let uu____4691 = eq_tm a b  in
          (match uu____4691 with
           | Equal  -> eq_args a11 b1
           | uu____4692 -> Unknown)
      | uu____4693 -> Unknown

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
      | (FStar_Pervasives_Native.None ,uu____4748) -> NotEqual
      | (uu____4755,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4785 -> NotEqual
  
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4802) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4808,uu____4809) ->
        unrefine t2
    | uu____4850 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4858 =
      let uu____4859 = FStar_Syntax_Subst.compress t  in
      uu____4859.FStar_Syntax_Syntax.n  in
    match uu____4858 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4863 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4878) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4883 ->
        let uu____4900 =
          let uu____4901 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4901 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4900 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4964,uu____4965) ->
        is_uvar t1
    | uu____5006 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5015 =
      let uu____5016 = unrefine t  in uu____5016.FStar_Syntax_Syntax.n  in
    match uu____5015 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head,uu____5022) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5048) -> is_unit t1
    | uu____5053 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5062 =
      let uu____5063 = FStar_Syntax_Subst.compress t  in
      uu____5063.FStar_Syntax_Syntax.n  in
    match uu____5062 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5068 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5077 =
      let uu____5078 = FStar_Syntax_Subst.compress e  in
      uu____5078.FStar_Syntax_Syntax.n  in
    match uu____5077 with
    | FStar_Syntax_Syntax.Tm_abs uu____5082 -> true
    | uu____5102 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5111 =
      let uu____5112 = FStar_Syntax_Subst.compress t  in
      uu____5112.FStar_Syntax_Syntax.n  in
    match uu____5111 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5116 -> true
    | uu____5132 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5142) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5148,uu____5149) ->
        pre_typ t2
    | uu____5190 -> t1
  
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
      let uu____5215 =
        let uu____5216 = un_uinst typ1  in uu____5216.FStar_Syntax_Syntax.n
         in
      match uu____5215 with
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let head1 = un_uinst head  in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5281 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5311 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5332,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5339) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5344,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5355,uu____5356,uu____5357,uu____5358,uu____5359) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5369,uu____5370,uu____5371,uu____5372) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5378,uu____5379,uu____5380,uu____5381,uu____5382) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5390,uu____5391) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5393,uu____5394) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5396 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5397 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5398 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5411 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5435 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5461  ->
    match uu___7_5461 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'uuuuuu5475 'uuuuuu5476 .
    ('uuuuuu5475 FStar_Syntax_Syntax.syntax * 'uuuuuu5476) ->
      FStar_Range.range
  =
  fun uu____5487  ->
    match uu____5487 with | (hd,uu____5495) -> hd.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'uuuuuu5509 'uuuuuu5510 .
    ('uuuuuu5509 FStar_Syntax_Syntax.syntax * 'uuuuuu5510) Prims.list ->
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
      | uu____5608 ->
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
      let uu____5667 =
        FStar_List.map
          (fun uu____5694  ->
             match uu____5694 with
             | (bv,aq) ->
                 let uu____5713 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5713, aq)) bs
         in
      mk_app f uu____5667
  
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
          (let uu____5764 =
             let uu____5770 =
               let uu____5772 =
                 let uu____5774 = FStar_Ident.ident_of_lid lid  in
                 FStar_Ident.text_of_id uu____5774  in
               mk_field_projector_name_from_string uu____5772 itext  in
             let uu____5775 = FStar_Ident.range_of_id i  in
             (uu____5770, uu____5775)  in
           FStar_Ident.mk_ident uu____5764)
         in
      let uu____5777 =
        let uu____5778 = FStar_Ident.ns_of_lid lid  in
        FStar_List.append uu____5778 [newi]  in
      FStar_Ident.lid_of_ids uu____5777
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5800 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5800
          then
            let uu____5803 =
              let uu____5809 =
                let uu____5811 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5811  in
              let uu____5814 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5809, uu____5814)  in
            FStar_Ident.mk_ident uu____5803
          else x.FStar_Syntax_Syntax.ppname  in
        mk_field_projector_name_from_ident lid nm
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5829) -> ses
    | uu____5838 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5853 = FStar_Syntax_Unionfind.find uv  in
      match uu____5853 with
      | FStar_Pervasives_Native.Some uu____5856 ->
          let uu____5857 =
            let uu____5859 =
              let uu____5861 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5861  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5859  in
          failwith uu____5857
      | uu____5866 -> FStar_Syntax_Unionfind.change uv t
  
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
            (let uu____5890 = FStar_Ident.text_of_id l1b  in
             let uu____5892 = FStar_Ident.text_of_id l2b  in
             uu____5890 = uu____5892)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5921 = FStar_Ident.text_of_id x1  in
                      let uu____5923 = FStar_Ident.text_of_id x2  in
                      uu____5921 = uu____5923) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5932 = FStar_Ident.text_of_id x1  in
                    let uu____5934 = FStar_Ident.text_of_id x2  in
                    uu____5932 = uu____5934) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5963 = FStar_Ident.text_of_id x1  in
                      let uu____5965 = FStar_Ident.text_of_id x2  in
                      uu____5963 = uu____5965) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5974 = FStar_Ident.text_of_id x1  in
                    let uu____5976 = FStar_Ident.text_of_id x2  in
                    uu____5974 = uu____5976) f1 f2)
      | uu____5979 -> q1 = q2
  
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
              let uu____6025 =
                let uu___1008_6026 = rc  in
                let uu____6027 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1008_6026.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6027;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1008_6026.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6025
           in
        match bs with
        | [] -> t
        | uu____6044 ->
            let body =
              let uu____6046 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6046  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6076 =
                   let uu____6083 =
                     let uu____6084 =
                       let uu____6103 =
                         let uu____6112 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6112 bs'  in
                       let uu____6127 = close_lopt lopt'  in
                       (uu____6103, t1, uu____6127)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6084  in
                   FStar_Syntax_Syntax.mk uu____6083  in
                 uu____6076 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6142 ->
                 let uu____6143 =
                   let uu____6150 =
                     let uu____6151 =
                       let uu____6170 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6179 = close_lopt lopt  in
                       (uu____6170, body, uu____6179)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6151  in
                   FStar_Syntax_Syntax.mk uu____6150  in
                 uu____6143 FStar_Pervasives_Native.None
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
      | uu____6235 ->
          let uu____6244 =
            let uu____6251 =
              let uu____6252 =
                let uu____6267 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6276 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6267, uu____6276)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6252  in
            FStar_Syntax_Syntax.mk uu____6251  in
          uu____6244 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6325 =
        let uu____6326 = FStar_Syntax_Subst.compress t  in
        uu____6326.FStar_Syntax_Syntax.n  in
      match uu____6325 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6356) ->
               let uu____6365 =
                 let uu____6366 = FStar_Syntax_Subst.compress tres  in
                 uu____6366.FStar_Syntax_Syntax.n  in
               (match uu____6365 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6409 -> t)
           | uu____6410 -> t)
      | uu____6411 -> t
  
let rec (canon_arrow :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____6424 =
      let uu____6425 = FStar_Syntax_Subst.compress t  in
      uu____6425.FStar_Syntax_Syntax.n  in
    match uu____6424 with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let cn =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Total (t1,u) ->
              let uu____6463 =
                let uu____6472 = canon_arrow t1  in (uu____6472, u)  in
              FStar_Syntax_Syntax.Total uu____6463
          | uu____6479 -> c.FStar_Syntax_Syntax.n  in
        let c1 =
          let uu___1052_6483 = c  in
          {
            FStar_Syntax_Syntax.n = cn;
            FStar_Syntax_Syntax.pos =
              (uu___1052_6483.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___1052_6483.FStar_Syntax_Syntax.vars)
          }  in
        flat_arrow bs c1
    | uu____6486 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6504 =
        let uu____6505 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6505 t.FStar_Syntax_Syntax.pos  in
      let uu____6506 =
        let uu____6513 =
          let uu____6514 =
            let uu____6521 =
              let uu____6524 =
                let uu____6525 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6525]  in
              FStar_Syntax_Subst.close uu____6524 t  in
            (b, uu____6521)  in
          FStar_Syntax_Syntax.Tm_refine uu____6514  in
        FStar_Syntax_Syntax.mk uu____6513  in
      uu____6506 FStar_Pervasives_Native.None uu____6504
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let (has_decreases : FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____6561 =
          FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
            (FStar_Util.find_opt
               (fun uu___8_6570  ->
                  match uu___8_6570 with
                  | FStar_Syntax_Syntax.DECREASES uu____6572 -> true
                  | uu____6576 -> false))
           in
        (match uu____6561 with
         | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES d) ->
             true
         | uu____6583 -> false)
    | uu____6587 -> false
  
let rec (arrow_formals_comp_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____6642 =
          (is_total_comp c) &&
            (let uu____6645 = has_decreases c  in
             Prims.op_Negation uu____6645)
           in
        if uu____6642
        then
          let uu____6660 = arrow_formals_comp_ln (comp_result c)  in
          (match uu____6660 with
           | (bs',k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6727;
           FStar_Syntax_Syntax.index = uu____6728;
           FStar_Syntax_Syntax.sort = s;_},uu____6730)
        ->
        let rec aux s1 k2 =
          let uu____6761 =
            let uu____6762 = FStar_Syntax_Subst.compress s1  in
            uu____6762.FStar_Syntax_Syntax.n  in
          match uu____6761 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6777 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6792;
                 FStar_Syntax_Syntax.index = uu____6793;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6795)
              -> aux s2 k2
          | uu____6803 ->
              let uu____6804 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6804)
           in
        aux s k1
    | uu____6819 ->
        let uu____6820 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6820)
  
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let uu____6845 = arrow_formals_comp_ln k  in
    match uu____6845 with | (bs,c) -> FStar_Syntax_Subst.open_comp bs c
  
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6900 = arrow_formals_comp_ln k  in
    match uu____6900 with | (bs,c) -> (bs, (comp_result c))
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6967 = arrow_formals_comp k  in
    match uu____6967 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7069 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7069 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____7093 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___9_7102  ->
                         match uu___9_7102 with
                         | FStar_Syntax_Syntax.DECREASES uu____7104 -> true
                         | uu____7108 -> false))
                  in
               (match uu____7093 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7143 ->
                    let uu____7146 = is_total_comp c1  in
                    if uu____7146
                    then
                      let uu____7165 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7165 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7258;
             FStar_Syntax_Syntax.index = uu____7259;
             FStar_Syntax_Syntax.sort = k2;_},uu____7261)
          -> arrow_until_decreases k2
      | uu____7269 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7290 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7290 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7344 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7365 =
                 FStar_Common.tabulate n_univs (fun uu____7371  -> false)  in
               let uu____7374 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7399  ->
                         match uu____7399 with
                         | (x,uu____7408) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7365 uu____7374)
           in
        ((n_univs + (FStar_List.length bs)), uu____7344)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7464 =
            let uu___1162_7465 = rc  in
            let uu____7466 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1162_7465.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7466;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1162_7465.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7464
      | uu____7475 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7509 =
        let uu____7510 =
          let uu____7513 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7513  in
        uu____7510.FStar_Syntax_Syntax.n  in
      match uu____7509 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7559 = aux t2 what  in
          (match uu____7559 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7631 -> ([], t1, abs_body_lcomp)  in
    let uu____7648 = aux t FStar_Pervasives_Native.None  in
    match uu____7648 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7696 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7696 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let no_acc uu____7730 =
      match uu____7730 with
      | (b,aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true )) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7744 -> aq  in
          (b, aq1)
       in
    let uu____7749 = arrow_formals_comp_ln t  in
    match uu____7749 with
    | (bs,c) ->
        (match bs with
         | [] -> t
         | uu____7786 ->
             let uu____7795 =
               let uu____7802 =
                 let uu____7803 =
                   let uu____7818 = FStar_List.map no_acc bs  in
                   (uu____7818, c)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____7803  in
               FStar_Syntax_Syntax.mk uu____7802  in
             uu____7795 FStar_Pervasives_Native.None
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
                    | (FStar_Pervasives_Native.None ,uu____7989) -> def
                    | (uu____8000,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____8012) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu____8028  ->
                                  FStar_Syntax_Syntax.U_name uu____8028))
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
            let uu____8110 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____8110 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____8145 ->
            let t' = arrow binders c  in
            let uu____8157 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____8157 with
             | (uvs1,t'1) ->
                 let uu____8178 =
                   let uu____8179 = FStar_Syntax_Subst.compress t'1  in
                   uu____8179.FStar_Syntax_Syntax.n  in
                 (match uu____8178 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8228 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8253 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Parser_Const.is_tuple_constructor_string uu____8253
    | uu____8255 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8266 -> false
  
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
      let uu____8329 =
        let uu____8330 = pre_typ t  in uu____8330.FStar_Syntax_Syntax.n  in
      match uu____8329 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8335 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8349 =
        let uu____8350 = pre_typ t  in uu____8350.FStar_Syntax_Syntax.n  in
      match uu____8349 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8354 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8356) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8382) ->
          is_constructed_typ t1 lid
      | uu____8387 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8400 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8401 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8402 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8404) -> get_tycon t2
    | uu____8429 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8437 =
      let uu____8438 = un_uinst t  in uu____8438.FStar_Syntax_Syntax.n  in
    match uu____8437 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8443 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8457 =
        let uu____8461 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8461  in
      match uu____8457 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8493 -> false
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
  fun uu____8512  ->
    let u =
      let uu____8518 =
        FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
      FStar_All.pipe_left
        (fun uu____8539  -> FStar_Syntax_Syntax.U_unif uu____8539) uu____8518
       in
    let uu____8540 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8540, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8553 = eq_tm a a'  in
      match uu____8553 with | Equal  -> true | uu____8556 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8561 =
    let uu____8568 =
      let uu____8569 =
        let uu____8570 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8570
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8569  in
    FStar_Syntax_Syntax.mk uu____8568  in
  uu____8561 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8683 =
            let uu____8686 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8687 =
              let uu____8694 =
                let uu____8695 =
                  let uu____8712 =
                    let uu____8723 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8732 =
                      let uu____8743 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8743]  in
                    uu____8723 :: uu____8732  in
                  (tand, uu____8712)  in
                FStar_Syntax_Syntax.Tm_app uu____8695  in
              FStar_Syntax_Syntax.mk uu____8694  in
            uu____8687 FStar_Pervasives_Native.None uu____8686  in
          FStar_Pervasives_Native.Some uu____8683
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8820 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8821 =
          let uu____8828 =
            let uu____8829 =
              let uu____8846 =
                let uu____8857 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8866 =
                  let uu____8877 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8877]  in
                uu____8857 :: uu____8866  in
              (op_t, uu____8846)  in
            FStar_Syntax_Syntax.Tm_app uu____8829  in
          FStar_Syntax_Syntax.mk uu____8828  in
        uu____8821 FStar_Pervasives_Native.None uu____8820
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8934 =
      let uu____8941 =
        let uu____8942 =
          let uu____8959 =
            let uu____8970 = FStar_Syntax_Syntax.as_arg phi  in [uu____8970]
             in
          (t_not, uu____8959)  in
        FStar_Syntax_Syntax.Tm_app uu____8942  in
      FStar_Syntax_Syntax.mk uu____8941  in
    uu____8934 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____9167 =
      let uu____9174 =
        let uu____9175 =
          let uu____9192 =
            let uu____9203 = FStar_Syntax_Syntax.as_arg e  in [uu____9203]
             in
          (b2t_v, uu____9192)  in
        FStar_Syntax_Syntax.Tm_app uu____9175  in
      FStar_Syntax_Syntax.mk uu____9174  in
    uu____9167 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9250 = head_and_args e  in
    match uu____9250 with
    | (hd,args) ->
        let uu____9295 =
          let uu____9310 =
            let uu____9311 = FStar_Syntax_Subst.compress hd  in
            uu____9311.FStar_Syntax_Syntax.n  in
          (uu____9310, args)  in
        (match uu____9295 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9328)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9363 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9385 =
      let uu____9386 = unmeta t  in uu____9386.FStar_Syntax_Syntax.n  in
    match uu____9385 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9391 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9414 = is_t_true t1  in
      if uu____9414
      then t2
      else
        (let uu____9421 = is_t_true t2  in
         if uu____9421 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9449 = is_t_true t1  in
      if uu____9449
      then t_true
      else
        (let uu____9456 = is_t_true t2  in
         if uu____9456 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9485 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9486 =
        let uu____9493 =
          let uu____9494 =
            let uu____9511 =
              let uu____9522 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9531 =
                let uu____9542 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9542]  in
              uu____9522 :: uu____9531  in
            (teq, uu____9511)  in
          FStar_Syntax_Syntax.Tm_app uu____9494  in
        FStar_Syntax_Syntax.mk uu____9493  in
      uu____9486 FStar_Pervasives_Native.None uu____9485
  
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
          let uu____9609 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9610 =
            let uu____9617 =
              let uu____9618 =
                let uu____9635 =
                  let uu____9646 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9655 =
                    let uu____9666 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9675 =
                      let uu____9686 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9686]  in
                    uu____9666 :: uu____9675  in
                  uu____9646 :: uu____9655  in
                (eq_inst, uu____9635)  in
              FStar_Syntax_Syntax.Tm_app uu____9618  in
            FStar_Syntax_Syntax.mk uu____9617  in
          uu____9610 FStar_Pervasives_Native.None uu____9609
  
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
        let uu____9763 =
          let uu____9770 =
            let uu____9771 =
              let uu____9788 =
                let uu____9799 = FStar_Syntax_Syntax.iarg t  in
                let uu____9808 =
                  let uu____9819 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9828 =
                    let uu____9839 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9839]  in
                  uu____9819 :: uu____9828  in
                uu____9799 :: uu____9808  in
              (t_has_type1, uu____9788)  in
            FStar_Syntax_Syntax.Tm_app uu____9771  in
          FStar_Syntax_Syntax.mk uu____9770  in
        uu____9763 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9916 =
          let uu____9923 =
            let uu____9924 =
              let uu____9941 =
                let uu____9952 = FStar_Syntax_Syntax.iarg t  in
                let uu____9961 =
                  let uu____9972 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9972]  in
                uu____9952 :: uu____9961  in
              (t_with_type1, uu____9941)  in
            FStar_Syntax_Syntax.Tm_app uu____9924  in
          FStar_Syntax_Syntax.mk uu____9923  in
        uu____9916 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____10019 =
    let uu____10026 =
      let uu____10027 =
        let uu____10034 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____10034, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____10027  in
    FStar_Syntax_Syntax.mk uu____10026  in
  uu____10019 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
        let uu____10117 =
          let uu____10124 =
            let uu____10125 =
              let uu____10142 =
                let uu____10153 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____10162 =
                  let uu____10173 =
                    let uu____10182 =
                      let uu____10183 =
                        let uu____10184 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10184]  in
                      abs uu____10183 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10182  in
                  [uu____10173]  in
                uu____10153 :: uu____10162  in
              (fa, uu____10142)  in
            FStar_Syntax_Syntax.Tm_app uu____10125  in
          FStar_Syntax_Syntax.mk uu____10124  in
        uu____10117 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10311 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10311
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10330 -> true
    | uu____10332 -> false
  
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
          let uu____10379 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10379, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10408 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10408, FStar_Pervasives_Native.None, t2)  in
        let uu____10422 =
          let uu____10423 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10423  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10422
  
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
      let uu____10499 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10502 =
        let uu____10513 = FStar_Syntax_Syntax.as_arg p  in [uu____10513]  in
      mk_app uu____10499 uu____10502
  
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
      let uu____10553 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10556 =
        let uu____10567 = FStar_Syntax_Syntax.as_arg p  in [uu____10567]  in
      mk_app uu____10553 uu____10556
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10602 = head_and_args t  in
    match uu____10602 with
    | (head,args) ->
        let head1 = unascribe head  in
        let head2 = un_uinst head1  in
        let uu____10651 =
          let uu____10666 =
            let uu____10667 = FStar_Syntax_Subst.compress head2  in
            uu____10667.FStar_Syntax_Syntax.n  in
          (uu____10666, args)  in
        (match uu____10651 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10686)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10752 =
                    let uu____10757 =
                      let uu____10758 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10758]  in
                    FStar_Syntax_Subst.open_term uu____10757 p  in
                  (match uu____10752 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10815 -> failwith "impossible"  in
                       let uu____10823 =
                         let uu____10825 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10825
                          in
                       if uu____10823
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10841 -> FStar_Pervasives_Native.None)
         | uu____10844 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10875 = head_and_args t  in
    match uu____10875 with
    | (head,args) ->
        let uu____10926 =
          let uu____10941 =
            let uu____10942 = FStar_Syntax_Subst.compress head  in
            uu____10942.FStar_Syntax_Syntax.n  in
          (uu____10941, args)  in
        (match uu____10926 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10964;
               FStar_Syntax_Syntax.vars = uu____10965;_},u::[]),(t1,uu____10968)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11015 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11050 = head_and_args t  in
    match uu____11050 with
    | (head,args) ->
        let uu____11101 =
          let uu____11116 =
            let uu____11117 = FStar_Syntax_Subst.compress head  in
            uu____11117.FStar_Syntax_Syntax.n  in
          (uu____11116, args)  in
        (match uu____11101 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____11139;
               FStar_Syntax_Syntax.vars = uu____11140;_},u::[]),(t1,uu____11143)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11190 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11218 =
      let uu____11235 = unmeta t  in head_and_args uu____11235  in
    match uu____11218 with
    | (head,uu____11238) ->
        let uu____11263 =
          let uu____11264 = un_uinst head  in
          uu____11264.FStar_Syntax_Syntax.n  in
        (match uu____11263 with
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
         | uu____11269 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11289 =
      let uu____11290 = FStar_Syntax_Subst.compress t  in
      uu____11290.FStar_Syntax_Syntax.n  in
    match uu____11289 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11396 =
          let uu____11401 =
            let uu____11402 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11402  in
          (b, uu____11401)  in
        FStar_Pervasives_Native.Some uu____11396
    | uu____11407 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11430 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11430
      (fun uu____11458  ->
         match uu____11458 with
         | (b,c) ->
             let uu____11477 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11477 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11540 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11577 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11577
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11629 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11672 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11713 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____12099) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____12111) ->
          unmeta_monadic t
      | uu____12124 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12193 =
        match uu____12193 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12231  ->
                   match uu____12231 with
                   | (lid,out_lid) ->
                       let uu____12240 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12240
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12267 = head_and_args t  in
      match uu____12267 with
      | (hd,args) ->
          let uu____12312 =
            let uu____12313 = un_uinst hd  in
            uu____12313.FStar_Syntax_Syntax.n  in
          (match uu____12312 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12319 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12328 = un_squash t  in
      FStar_Util.bind_opt uu____12328
        (fun t1  ->
           let uu____12344 = head_and_args' t1  in
           match uu____12344 with
           | (hd,args) ->
               let uu____12383 =
                 let uu____12384 = un_uinst hd  in
                 uu____12384.FStar_Syntax_Syntax.n  in
               (match uu____12383 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12390 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12431,pats)) ->
          let uu____12469 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12469)
      | uu____12482 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12549 = head_and_args t1  in
        match uu____12549 with
        | (t2,args) ->
            let uu____12604 = un_uinst t2  in
            let uu____12605 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12646  ->
                      match uu____12646 with
                      | (t3,imp) ->
                          let uu____12665 = unascribe t3  in
                          (uu____12665, imp)))
               in
            (uu____12604, uu____12605)
         in
      let rec aux qopt out t1 =
        let uu____12716 = let uu____12740 = flat t1  in (qopt, uu____12740)
           in
        match uu____12716 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12780;
                 FStar_Syntax_Syntax.vars = uu____12781;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12784);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12785;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12786;_},uu____12787)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12889;
                 FStar_Syntax_Syntax.vars = uu____12890;_},uu____12891::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12894);
                  FStar_Syntax_Syntax.pos = uu____12895;
                  FStar_Syntax_Syntax.vars = uu____12896;_},uu____12897)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13014;
               FStar_Syntax_Syntax.vars = uu____13015;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____13018);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____13019;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____13020;_},uu____13021)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13114 =
              let uu____13118 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13118  in
            aux uu____13114 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13128;
               FStar_Syntax_Syntax.vars = uu____13129;_},uu____13130::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____13133);
                FStar_Syntax_Syntax.pos = uu____13134;
                FStar_Syntax_Syntax.vars = uu____13135;_},uu____13136)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13245 =
              let uu____13249 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13249  in
            aux uu____13245 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13259) ->
            let bs = FStar_List.rev out  in
            let uu____13312 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13312 with
             | (bs1,t2) ->
                 let uu____13321 = patterns t2  in
                 (match uu____13321 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13371 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13426 = un_squash t  in
      FStar_Util.bind_opt uu____13426
        (fun t1  ->
           let uu____13441 = arrow_one t1  in
           match uu____13441 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13456 =
                 let uu____13458 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13458  in
               if uu____13456
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13468 = comp_to_comp_typ_nouniv c  in
                    uu____13468.FStar_Syntax_Syntax.result_typ  in
                  let uu____13469 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13469
                  then
                    let uu____13476 = patterns q  in
                    match uu____13476 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13539 =
                       let uu____13540 =
                         let uu____13545 =
                           let uu____13546 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13557 =
                             let uu____13568 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13568]  in
                           uu____13546 :: uu____13557  in
                         (FStar_Parser_Const.imp_lid, uu____13545)  in
                       BaseConn uu____13540  in
                     FStar_Pervasives_Native.Some uu____13539))
           | uu____13601 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13609 = un_squash t  in
      FStar_Util.bind_opt uu____13609
        (fun t1  ->
           let uu____13640 = head_and_args' t1  in
           match uu____13640 with
           | (hd,args) ->
               let uu____13679 =
                 let uu____13694 =
                   let uu____13695 = un_uinst hd  in
                   uu____13695.FStar_Syntax_Syntax.n  in
                 (uu____13694, args)  in
               (match uu____13679 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13712)::(a2,uu____13714)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13765 =
                      let uu____13766 = FStar_Syntax_Subst.compress a2  in
                      uu____13766.FStar_Syntax_Syntax.n  in
                    (match uu____13765 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13773) ->
                         let uu____13808 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13808 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13861 -> failwith "impossible"  in
                              let uu____13869 = patterns q1  in
                              (match uu____13869 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13930 -> FStar_Pervasives_Native.None)
                | uu____13931 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13954 = destruct_sq_forall phi  in
          (match uu____13954 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13964  ->
                    FStar_Pervasives_Native.Some uu____13964)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13971 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13977 = destruct_sq_exists phi  in
          (match uu____13977 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13987  ->
                    FStar_Pervasives_Native.Some uu____13987)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13994 -> f1)
      | uu____13997 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____14001 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____14001
      (fun uu____14006  ->
         let uu____14007 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____14007
           (fun uu____14012  ->
              let uu____14013 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____14013
                (fun uu____14018  ->
                   let uu____14019 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____14019
                     (fun uu____14024  ->
                        let uu____14025 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____14025
                          (fun uu____14029  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____14047 =
            let uu____14052 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____14052  in
          let uu____14053 =
            let uu____14054 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____14054  in
          let uu____14057 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____14047 a.FStar_Syntax_Syntax.action_univs uu____14053
            FStar_Parser_Const.effect_Tot_lid uu____14057 [] pos
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
    let uu____14083 =
      let uu____14090 =
        let uu____14091 =
          let uu____14108 =
            let uu____14119 = FStar_Syntax_Syntax.as_arg t  in [uu____14119]
             in
          (reify_, uu____14108)  in
        FStar_Syntax_Syntax.Tm_app uu____14091  in
      FStar_Syntax_Syntax.mk uu____14090  in
    uu____14083 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14171 =
        let uu____14178 =
          let uu____14179 =
            let uu____14180 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14180  in
          FStar_Syntax_Syntax.Tm_constant uu____14179  in
        FStar_Syntax_Syntax.mk uu____14178  in
      uu____14171 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14182 =
      let uu____14189 =
        let uu____14190 =
          let uu____14207 =
            let uu____14218 = FStar_Syntax_Syntax.as_arg t  in [uu____14218]
             in
          (reflect_, uu____14207)  in
        FStar_Syntax_Syntax.Tm_app uu____14190  in
      FStar_Syntax_Syntax.mk uu____14189  in
    uu____14182 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14262 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14279 = unfold_lazy i  in delta_qualifier uu____14279
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14281 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14282 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14283 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14306 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14319 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14320 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14327 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14328 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14344) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14349;
           FStar_Syntax_Syntax.index = uu____14350;
           FStar_Syntax_Syntax.sort = t2;_},uu____14352)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14361) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14367,uu____14368) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14410) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14435,t2,uu____14437) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14462,t2) -> delta_qualifier t2
  
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
    let uu____14501 = delta_qualifier t  in incr_delta_depth uu____14501
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14509 =
      let uu____14510 = FStar_Syntax_Subst.compress t  in
      uu____14510.FStar_Syntax_Syntax.n  in
    match uu____14509 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14515 -> false
  
let rec apply_last :
  'uuuuuu14524 .
    ('uuuuuu14524 -> 'uuuuuu14524) ->
      'uuuuuu14524 Prims.list -> 'uuuuuu14524 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14550 = f a  in [uu____14550]
      | x::xs -> let uu____14555 = apply_last f xs  in x :: uu____14555
  
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
          let uu____14610 =
            let uu____14617 =
              let uu____14618 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14618  in
            FStar_Syntax_Syntax.mk uu____14617  in
          uu____14610 FStar_Pervasives_Native.None rng  in
        let cons args pos =
          let uu____14632 =
            let uu____14637 =
              let uu____14638 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14638
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14637 args  in
          uu____14632 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14652 =
            let uu____14657 =
              let uu____14658 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14658
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14657 args  in
          uu____14652 FStar_Pervasives_Native.None pos  in
        let uu____14659 =
          let uu____14660 =
            let uu____14661 = FStar_Syntax_Syntax.iarg typ  in [uu____14661]
             in
          nil uu____14660 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14695 =
                 let uu____14696 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14705 =
                   let uu____14716 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14725 =
                     let uu____14736 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14736]  in
                   uu____14716 :: uu____14725  in
                 uu____14696 :: uu____14705  in
               cons uu____14695 t.FStar_Syntax_Syntax.pos) l uu____14659
  
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
        | uu____14845 -> false
  
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
          | uu____14959 -> false
  
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
        | uu____15125 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15163 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15163
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
        let t11 = let uu____15367 = unmeta_safe t1  in canon_app uu____15367
           in
        let t21 = let uu____15373 = unmeta_safe t2  in canon_app uu____15373
           in
        let uu____15376 =
          let uu____15381 =
            let uu____15382 =
              let uu____15385 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15385  in
            uu____15382.FStar_Syntax_Syntax.n  in
          let uu____15386 =
            let uu____15387 =
              let uu____15390 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15390  in
            uu____15387.FStar_Syntax_Syntax.n  in
          (uu____15381, uu____15386)  in
        match uu____15376 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15392,uu____15393) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15402,FStar_Syntax_Syntax.Tm_uinst uu____15403) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15412,uu____15413) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15430,FStar_Syntax_Syntax.Tm_delayed uu____15431) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15448,uu____15449) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15478,FStar_Syntax_Syntax.Tm_ascribed uu____15479) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15518 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15518
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15523 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15523
        | (FStar_Syntax_Syntax.Tm_type
           uu____15526,FStar_Syntax_Syntax.Tm_type uu____15527) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15585 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15585) &&
              (let uu____15595 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15595)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15644 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15644) &&
              (let uu____15654 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15654)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15671 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15671) &&
              (let uu____15675 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15675)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15732 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15732) &&
              (let uu____15736 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15736)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15825 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15825) &&
              (let uu____15829 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15829)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15846,uu____15847) ->
            let uu____15848 =
              let uu____15850 = unlazy t11  in
              term_eq_dbg dbg uu____15850 t21  in
            check "lazy_l" uu____15848
        | (uu____15852,FStar_Syntax_Syntax.Tm_lazy uu____15853) ->
            let uu____15854 =
              let uu____15856 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15856  in
            check "lazy_r" uu____15854
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15901 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15901))
              &&
              (let uu____15905 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15905)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15909),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15911)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15971 =
               let uu____15973 = eq_quoteinfo qi1 qi2  in uu____15973 = Equal
                in
             check "tm_quoted qi" uu____15971) &&
              (let uu____15976 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15976)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____16006 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____16006) &&
                   (let uu____16010 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____16010)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____16029 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____16029) &&
                    (let uu____16033 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____16033))
                   &&
                   (let uu____16037 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____16037)
             | uu____16040 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____16046) -> fail "unk"
        | (uu____16048,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____16050,uu____16051) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____16053,uu____16054) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____16056,uu____16057) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____16059,uu____16060) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____16062,uu____16063) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____16065,uu____16066) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____16086,uu____16087) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____16103,uu____16104) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____16112,uu____16113) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____16131,uu____16132) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16156,uu____16157) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16172,uu____16173) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16187,uu____16188) ->
            fail "bottom"
        | (uu____16196,FStar_Syntax_Syntax.Tm_bvar uu____16197) ->
            fail "bottom"
        | (uu____16199,FStar_Syntax_Syntax.Tm_name uu____16200) ->
            fail "bottom"
        | (uu____16202,FStar_Syntax_Syntax.Tm_fvar uu____16203) ->
            fail "bottom"
        | (uu____16205,FStar_Syntax_Syntax.Tm_constant uu____16206) ->
            fail "bottom"
        | (uu____16208,FStar_Syntax_Syntax.Tm_type uu____16209) ->
            fail "bottom"
        | (uu____16211,FStar_Syntax_Syntax.Tm_abs uu____16212) ->
            fail "bottom"
        | (uu____16232,FStar_Syntax_Syntax.Tm_arrow uu____16233) ->
            fail "bottom"
        | (uu____16249,FStar_Syntax_Syntax.Tm_refine uu____16250) ->
            fail "bottom"
        | (uu____16258,FStar_Syntax_Syntax.Tm_app uu____16259) ->
            fail "bottom"
        | (uu____16277,FStar_Syntax_Syntax.Tm_match uu____16278) ->
            fail "bottom"
        | (uu____16302,FStar_Syntax_Syntax.Tm_let uu____16303) ->
            fail "bottom"
        | (uu____16318,FStar_Syntax_Syntax.Tm_uvar uu____16319) ->
            fail "bottom"
        | (uu____16333,FStar_Syntax_Syntax.Tm_meta uu____16334) ->
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
               let uu____16369 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16369)
          (fun q1  ->
             fun q2  ->
               let uu____16381 =
                 let uu____16383 = eq_aqual q1 q2  in uu____16383 = Equal  in
               check "arg qual" uu____16381) a1 a2

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
               let uu____16408 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16408)
          (fun q1  ->
             fun q2  ->
               let uu____16420 =
                 let uu____16422 = eq_aqual q1 q2  in uu____16422 = Equal  in
               check "binder qual" uu____16420) b1 b2

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
        ((let uu____16436 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16436) &&
           (let uu____16440 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16440))
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
    fun uu____16450  ->
      fun uu____16451  ->
        match (uu____16450, uu____16451) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16578 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16578) &&
               (let uu____16582 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16582))
              &&
              (let uu____16586 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16628 -> false  in
               check "branch when" uu____16586)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16649 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16649) &&
           (let uu____16658 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16658))
          &&
          (let uu____16662 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16662)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16679 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16679 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16733 ->
        let uu____16748 =
          let uu____16750 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16750  in
        Prims.int_one + uu____16748
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16753 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16753
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16757 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16757
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16766 = sizeof t1  in (FStar_List.length us) + uu____16766
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16770) ->
        let uu____16795 = sizeof t1  in
        let uu____16797 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16812  ->
                 match uu____16812 with
                 | (bv,uu____16822) ->
                     let uu____16827 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16827) Prims.int_zero bs
           in
        uu____16795 + uu____16797
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____16856 = sizeof hd  in
        let uu____16858 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16873  ->
                 match uu____16873 with
                 | (arg,uu____16883) ->
                     let uu____16888 = sizeof arg  in acc + uu____16888)
            Prims.int_zero args
           in
        uu____16856 + uu____16858
    | uu____16891 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16905 =
        let uu____16906 = un_uinst t  in uu____16906.FStar_Syntax_Syntax.n
         in
      match uu____16905 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16911 -> false
  
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
           let uu____16972 = head_and_args t  in
           match uu____16972 with
           | (head,args) ->
               let uu____17027 =
                 let uu____17028 = FStar_Syntax_Subst.compress head  in
                 uu____17028.FStar_Syntax_Syntax.n  in
               (match uu____17027 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____17054 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____17087 = is_fvar attr a  in Prims.op_Negation uu____17087)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      FStar_Errors.set_option_warning_callback_range
        (FStar_Pervasives_Native.Some r);
      (let set_options s =
         let uu____17109 = FStar_Options.set_options s  in
         match uu____17109 with
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
           ((let uu____17123 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____17123 (fun uu____17125  -> ()));
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
           let uu____17139 = FStar_Options.internal_pop ()  in
           if uu____17139
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
    | FStar_Syntax_Syntax.Tm_delayed uu____17171 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17190 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17205 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17206 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17207 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17216) ->
        let uu____17241 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17241 with
         | (bs1,t2) ->
             let uu____17250 =
               FStar_List.collect
                 (fun uu____17262  ->
                    match uu____17262 with
                    | (b,uu____17272) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17277 = unbound_variables t2  in
             FStar_List.append uu____17250 uu____17277)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17302 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17302 with
         | (bs1,c1) ->
             let uu____17311 =
               FStar_List.collect
                 (fun uu____17323  ->
                    match uu____17323 with
                    | (b,uu____17333) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17338 = unbound_variables_comp c1  in
             FStar_List.append uu____17311 uu____17338)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17347 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17347 with
         | (bs,t2) ->
             let uu____17370 =
               FStar_List.collect
                 (fun uu____17382  ->
                    match uu____17382 with
                    | (b1,uu____17392) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17397 = unbound_variables t2  in
             FStar_List.append uu____17370 uu____17397)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17426 =
          FStar_List.collect
            (fun uu____17440  ->
               match uu____17440 with
               | (x,uu____17452) -> unbound_variables x) args
           in
        let uu____17461 = unbound_variables t1  in
        FStar_List.append uu____17426 uu____17461
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17502 = unbound_variables t1  in
        let uu____17505 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17520 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17520 with
                  | (p,wopt,t2) ->
                      let uu____17542 = unbound_variables t2  in
                      let uu____17545 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17542 uu____17545))
           in
        FStar_List.append uu____17502 uu____17505
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17559) ->
        let uu____17600 = unbound_variables t1  in
        let uu____17603 =
          let uu____17606 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17637 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17606 uu____17637  in
        FStar_List.append uu____17600 uu____17603
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17678 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17681 =
          let uu____17684 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17687 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17692 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17694 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17694 with
                 | (uu____17715,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17684 uu____17687  in
        FStar_List.append uu____17678 uu____17681
    | FStar_Syntax_Syntax.Tm_let ((uu____17717,lbs),t1) ->
        let uu____17737 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17737 with
         | (lbs1,t2) ->
             let uu____17752 = unbound_variables t2  in
             let uu____17755 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17762 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17765 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17762 uu____17765) lbs1
                in
             FStar_List.append uu____17752 uu____17755)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17782 = unbound_variables t1  in
        let uu____17785 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17790,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17845  ->
                      match uu____17845 with
                      | (a,uu____17857) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17866,uu____17867,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17873,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17879 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17888 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17889 -> []  in
        FStar_List.append uu____17782 uu____17785

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17896) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17906) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17916 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17919 =
          FStar_List.collect
            (fun uu____17933  ->
               match uu____17933 with
               | (a,uu____17945) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17916 uu____17919

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
            let uu____18060 = head_and_args h  in
            (match uu____18060 with
             | (head,args) ->
                 let uu____18121 =
                   let uu____18122 = FStar_Syntax_Subst.compress head  in
                   uu____18122.FStar_Syntax_Syntax.n  in
                 (match uu____18121 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18175 -> aux (h :: acc) t))
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
      let uu____18199 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18199 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2518_18241 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2518_18241.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2518_18241.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2518_18241.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2518_18241.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2518_18241.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18249 =
      let uu____18250 = FStar_Syntax_Subst.compress t  in
      uu____18250.FStar_Syntax_Syntax.n  in
    match uu____18249 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18254,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18282)::uu____18283 ->
                  let pats' = unmeta pats  in
                  let uu____18343 = head_and_args pats'  in
                  (match uu____18343 with
                   | (head,uu____18362) ->
                       let uu____18387 =
                         let uu____18388 = un_uinst head  in
                         uu____18388.FStar_Syntax_Syntax.n  in
                       (match uu____18387 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18393 -> false))
              | uu____18395 -> false)
         | uu____18407 -> false)
    | uu____18409 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18425 =
      let uu____18442 = unmeta e  in head_and_args uu____18442  in
    match uu____18425 with
    | (head,args) ->
        let uu____18473 =
          let uu____18488 =
            let uu____18489 = un_uinst head  in
            uu____18489.FStar_Syntax_Syntax.n  in
          (uu____18488, args)  in
        (match uu____18473 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18507) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18531::(hd,uu____18533)::(tl,uu____18535)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18602 =
               let uu____18605 =
                 let uu____18608 = list_elements tl  in
                 FStar_Util.must uu____18608  in
               hd :: uu____18605  in
             FStar_Pervasives_Native.Some uu____18602
         | uu____18617 -> FStar_Pervasives_Native.None)
  
let (unthunk : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____18640 =
      let uu____18641 = FStar_Syntax_Subst.compress t  in
      uu____18641.FStar_Syntax_Syntax.n  in
    match uu____18640 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18646) ->
        let uu____18681 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18681 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18713 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18713
             then
               let uu____18718 =
                 let uu____18729 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18729]  in
               mk_app t uu____18718
             else e1)
    | uu____18756 ->
        let uu____18757 =
          let uu____18768 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18768]  in
        mk_app t uu____18757
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) = fun t  -> unthunk t 
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18829 = list_elements e  in
        match uu____18829 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18864 =
          let uu____18881 = unmeta p  in
          FStar_All.pipe_right uu____18881 head_and_args  in
        match uu____18864 with
        | (head,args) ->
            let uu____18932 =
              let uu____18947 =
                let uu____18948 = un_uinst head  in
                uu____18948.FStar_Syntax_Syntax.n  in
              (uu____18947, args)  in
            (match uu____18932 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18970,uu____18971)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____19023 ->
                 let uu____19038 =
                   let uu____19044 =
                     let uu____19046 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____19046
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____19044)  in
                 FStar_Errors.raise_error uu____19038
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____19089 =
            let uu____19106 = unmeta t1  in
            FStar_All.pipe_right uu____19106 head_and_args  in
          match uu____19089 with
          | (head,args) ->
              let uu____19153 =
                let uu____19168 =
                  let uu____19169 = un_uinst head  in
                  uu____19169.FStar_Syntax_Syntax.n  in
                (uu____19168, args)  in
              (match uu____19153 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19188)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19225 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19255 = smt_pat_or t1  in
            (match uu____19255 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19277 = list_elements1 e  in
                 FStar_All.pipe_right uu____19277
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19307 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19307
                           (FStar_List.map one_pat)))
             | uu____19336 ->
                 let uu____19341 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19341])
        | uu____19396 ->
            let uu____19399 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19399]
         in
      let uu____19454 =
        let uu____19485 =
          let uu____19486 = FStar_Syntax_Subst.compress t  in
          uu____19486.FStar_Syntax_Syntax.n  in
        match uu____19485 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19541 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19541 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19608;
                        FStar_Syntax_Syntax.effect_name = uu____19609;
                        FStar_Syntax_Syntax.result_typ = uu____19610;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19612)::(post,uu____19614)::(pats,uu____19616)::[];
                        FStar_Syntax_Syntax.flags = uu____19617;_}
                      ->
                      let uu____19678 = lemma_pats pats  in
                      (binders1, pre, post, uu____19678)
                  | uu____19713 -> failwith "impos"))
        | uu____19745 -> failwith "Impos"  in
      match uu____19454 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19829 =
              let uu____19836 =
                let uu____19837 =
                  let uu____19844 = mk_imp pre post1  in
                  let uu____19847 =
                    let uu____19848 =
                      let uu____19869 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19869, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19848  in
                  (uu____19844, uu____19847)  in
                FStar_Syntax_Syntax.Tm_meta uu____19837  in
              FStar_Syntax_Syntax.mk uu____19836  in
            uu____19829 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19893 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19893 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19923 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19934 -> true
    | uu____19936 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19947 -> true
    | uu____19949 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19967 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19968 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19969 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19970 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19971 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19972 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19973 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19974 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19977 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19980 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19967;
        FStar_Syntax_Syntax.bind_wp = uu____19968;
        FStar_Syntax_Syntax.stronger = uu____19969;
        FStar_Syntax_Syntax.if_then_else = uu____19970;
        FStar_Syntax_Syntax.ite_wp = uu____19971;
        FStar_Syntax_Syntax.close_wp = uu____19972;
        FStar_Syntax_Syntax.trivial = uu____19973;
        FStar_Syntax_Syntax.repr = uu____19974;
        FStar_Syntax_Syntax.return_repr = uu____19977;
        FStar_Syntax_Syntax.bind_repr = uu____19980
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____20012 =
        match uu____20012 with
        | (ts1,ts2) ->
            let uu____20023 = f ts1  in
            let uu____20024 = f ts2  in (uu____20023, uu____20024)
         in
      let uu____20025 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____20030 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____20035 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____20040 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____20045 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____20025;
        FStar_Syntax_Syntax.l_return = uu____20030;
        FStar_Syntax_Syntax.l_bind = uu____20035;
        FStar_Syntax_Syntax.l_subcomp = uu____20040;
        FStar_Syntax_Syntax.l_if_then_else = uu____20045
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
          let uu____20067 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____20067
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____20069 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____20069
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____20071 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____20071
  
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
    | uu____20086 -> FStar_Pervasives_Native.None
  
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
        let uu____20100 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20100
          (fun uu____20107  -> FStar_Pervasives_Native.Some uu____20107)
  
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
        let uu____20147 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20147
          (fun uu____20154  -> FStar_Pervasives_Native.Some uu____20154)
  
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
        let uu____20168 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20168
          (fun uu____20175  -> FStar_Pervasives_Native.Some uu____20175)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20189  -> FStar_Pervasives_Native.Some uu____20189)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20193  -> FStar_Pervasives_Native.Some uu____20193)
    | uu____20194 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20206 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20206
          (fun uu____20213  -> FStar_Pervasives_Native.Some uu____20213)
    | uu____20214 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20228  -> FStar_Pervasives_Native.Some uu____20228)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20232  -> FStar_Pervasives_Native.Some uu____20232)
    | uu____20233 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20247  -> FStar_Pervasives_Native.Some uu____20247)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20251  -> FStar_Pervasives_Native.Some uu____20251)
    | uu____20252 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20276 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20277 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20279 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20279
          (fun uu____20286  -> FStar_Pervasives_Native.Some uu____20286)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun uu____20300  -> FStar_Pervasives_Native.Some uu____20300)
    | uu____20301 -> FStar_Pervasives_Native.None
  