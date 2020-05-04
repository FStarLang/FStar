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
          let uu____602 =
            let uu____617 = name_binders binders  in (uu____617, comp)  in
          FStar_Syntax_Syntax.Tm_arrow uu____602  in
        FStar_Syntax_Syntax.mk uu____601 t.FStar_Syntax_Syntax.pos
    | uu____636 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____673  ->
            match uu____673 with
            | (t,imp) ->
                let uu____684 =
                  let uu____685 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____685
                   in
                (uu____684, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____740  ->
            match uu____740 with
            | (t,imp) ->
                let uu____757 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____757, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____770 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____770
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'uuuuuu782 . 'uuuuuu782 -> 'uuuuuu782 Prims.list =
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
          (fun uu____908  ->
             fun uu____909  ->
               match (uu____908, uu____909) with
               | ((x,uu____935),(y,uu____937)) ->
                   let uu____958 =
                     let uu____965 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____965)  in
                   FStar_Syntax_Syntax.NT uu____958) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____981) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____987,uu____988) -> unmeta e2
    | uu____1029 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____1043 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____1050 -> e1
         | uu____1059 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1061,uu____1062) ->
        unmeta_safe e2
    | uu____1103 -> e1
  
let (unmeta_lift : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1110 =
      let uu____1111 = FStar_Syntax_Subst.compress t  in
      uu____1111.FStar_Syntax_Syntax.n  in
    match uu____1110 with
    | FStar_Syntax_Syntax.Tm_meta
        (t1,FStar_Syntax_Syntax.Meta_monadic_lift uu____1115) -> t1
    | uu____1128 -> t
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_name uu____1147 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_unif uu____1150 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_max uu____1163 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_zero  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1171 = univ_kernel u1  in
        (match uu____1171 with | (k,n) -> (k, (n + Prims.int_one)))
    | FStar_Syntax_Syntax.U_bvar uu____1188 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____1203 = univ_kernel u  in FStar_Pervasives_Native.snd uu____1203
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      let rec compare_kernel uk1 uk2 =
        match (uk1, uk2) with
        | (FStar_Syntax_Syntax.U_bvar uu____1236,uu____1237) ->
            failwith "Impossible: compare_kernel bvar"
        | (uu____1241,FStar_Syntax_Syntax.U_bvar uu____1242) ->
            failwith "Impossible: compare_kernel bvar"
        | (FStar_Syntax_Syntax.U_succ uu____1246,uu____1247) ->
            failwith "Impossible: compare_kernel succ"
        | (uu____1250,FStar_Syntax_Syntax.U_succ uu____1251) ->
            failwith "Impossible: compare_kernel succ"
        | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_unknown ,uu____1255) -> ~- Prims.int_one
        | (uu____1257,FStar_Syntax_Syntax.U_unknown ) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_zero ,uu____1260) -> ~- Prims.int_one
        | (uu____1262,FStar_Syntax_Syntax.U_zero ) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
            let uu____1266 = FStar_Ident.text_of_id u11  in
            let uu____1268 = FStar_Ident.text_of_id u21  in
            FStar_String.compare uu____1266 uu____1268
        | (FStar_Syntax_Syntax.U_name uu____1270,uu____1271) ->
            ~- Prims.int_one
        | (uu____1273,FStar_Syntax_Syntax.U_name uu____1274) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
            let uu____1298 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
            let uu____1300 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
            uu____1298 - uu____1300
        | (FStar_Syntax_Syntax.U_unif uu____1302,uu____1303) ->
            ~- Prims.int_one
        | (uu____1315,FStar_Syntax_Syntax.U_unif uu____1316) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
            let n1 = FStar_List.length us1  in
            let n2 = FStar_List.length us2  in
            if n1 <> n2
            then n1 - n2
            else
              (let copt =
                 let uu____1344 = FStar_List.zip us1 us2  in
                 FStar_Util.find_map uu____1344
                   (fun uu____1360  ->
                      match uu____1360 with
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
      let uu____1388 = univ_kernel u1  in
      match uu____1388 with
      | (uk1,n1) ->
          let uu____1399 = univ_kernel u2  in
          (match uu____1399 with
           | (uk2,n2) ->
               let uu____1410 = compare_kernel uk1 uk2  in
               (match uu____1410 with
                | uu____1413 when uu____1413 = Prims.int_zero -> n1 - n2
                | n -> n))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1428 = compare_univs u1 u2  in uu____1428 = Prims.int_zero
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1447 =
        let uu____1448 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1448;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1447
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1468 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1477 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1500 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1509 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1536 =
          let uu____1537 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1537  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1536;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1566 =
          let uu____1567 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1567  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1566;
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
      let uu___239_1603 = c  in
      let uu____1604 =
        let uu____1605 =
          let uu___241_1606 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___241_1606.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___241_1606.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___241_1606.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___241_1606.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1605  in
      {
        FStar_Syntax_Syntax.n = uu____1604;
        FStar_Syntax_Syntax.pos = (uu___239_1603.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___239_1603.FStar_Syntax_Syntax.vars)
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
    | uu____1646 ->
        failwith "Assertion failed: Computation type without universe"
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1668)::[] -> wp
      | uu____1693 ->
          let uu____1704 =
            let uu____1706 =
              FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name  in
            let uu____1708 =
              let uu____1710 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length
                 in
              FStar_All.pipe_right uu____1710 FStar_Util.string_of_int  in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args"
              uu____1706 uu____1708
             in
          failwith uu____1704
       in
    let uu____1734 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1734, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1748 -> true
    | FStar_Syntax_Syntax.GTotal uu____1758 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1783  ->
               match uu___0_1783 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1787 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1804  ->
            match uu___1_1804 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1808 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1840 -> true
    | FStar_Syntax_Syntax.GTotal uu____1850 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_1865  ->
                   match uu___2_1865 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1868 -> false)))
  
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
    let uu____1909 =
      let uu____1910 = FStar_Syntax_Subst.compress t  in
      uu____1910.FStar_Syntax_Syntax.n  in
    match uu____1909 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1914,c) -> is_pure_or_ghost_comp c
    | uu____1936 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1951 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1960 =
      let uu____1961 = FStar_Syntax_Subst.compress t  in
      uu____1961.FStar_Syntax_Syntax.n  in
    match uu____1960 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1965,c) -> is_lemma_comp c
    | uu____1987 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1995 =
      let uu____1996 = FStar_Syntax_Subst.compress t  in
      uu____1996.FStar_Syntax_Syntax.n  in
    match uu____1995 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____2000) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____2026) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2063,t1,uu____2065) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2091,uu____2092) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2134) -> head_of t1
    | uu____2139 -> t
  
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
    | uu____2217 -> (t1, [])
  
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
        let uu____2299 = head_and_args' head  in
        (match uu____2299 with
         | (head1,args') -> (head1, (FStar_List.append args' args)))
    | uu____2368 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2395) ->
        FStar_Syntax_Subst.compress t2
    | uu____2400 -> t1
  
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
                (fun uu___3_2418  ->
                   match uu___3_2418 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2421 -> false)))
    | uu____2423 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2440) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2450) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2479 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2488 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___380_2500 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___380_2500.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___380_2500.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___380_2500.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___380_2500.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2516  ->
            match uu___4_2516 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2520 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2528 -> []
    | FStar_Syntax_Syntax.GTotal uu____2545 -> []
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
    | uu____2589 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2599,uu____2600) ->
        unascribe e2
    | uu____2641 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2694,uu____2695) ->
          ascribe t' k
      | uu____2736 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2763 =
      let uu____2772 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2772  in
    uu____2763 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2828 =
      let uu____2829 = FStar_Syntax_Subst.compress t  in
      uu____2829.FStar_Syntax_Syntax.n  in
    match uu____2828 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2833 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2833
    | uu____2834 -> t
  
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2841 =
      let uu____2842 = FStar_Syntax_Subst.compress t  in
      uu____2842.FStar_Syntax_Syntax.n  in
    match uu____2841 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2846 ->
             let uu____2855 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____2855
         | uu____2856 -> t)
    | uu____2857 -> t
  
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
      | uu____2882 -> false
  
let unlazy_as_t :
  'uuuuuu2895 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'uuuuuu2895
  =
  fun k  ->
    fun t  ->
      let uu____2906 =
        let uu____2907 = FStar_Syntax_Subst.compress t  in
        uu____2907.FStar_Syntax_Syntax.n  in
      match uu____2906 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2912;
            FStar_Syntax_Syntax.rng = uu____2913;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____2916 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2957 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2957;
              FStar_Syntax_Syntax.lkind = k;
              FStar_Syntax_Syntax.ltyp = typ;
              FStar_Syntax_Syntax.rng = rng
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i) rng
  
let (canon_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____2968 =
      let uu____2983 = unascribe t  in head_and_args' uu____2983  in
    match uu____2968 with
    | (hd,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd args t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____3015 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____3026 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____3037 -> false
  
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
      | (NotEqual ,uu____3087) -> NotEqual
      | (uu____3088,NotEqual ) -> NotEqual
      | (Unknown ,uu____3089) -> Unknown
      | (uu____3090,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___5_3195 = if uu___5_3195 then Equal else Unknown  in
      let equal_iff uu___6_3206 = if uu___6_3206 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____3227 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3249 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3249
        then
          let uu____3253 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3330  ->
                    match uu____3330 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3371 = eq_tm a1 a2  in
                        eq_inj acc uu____3371) Equal) uu____3253
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3385 =
          let uu____3402 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3402 head_and_args  in
        match uu____3385 with
        | (head1,args1) ->
            let uu____3455 =
              let uu____3472 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3472 head_and_args  in
            (match uu____3455 with
             | (head2,args2) ->
                 let uu____3525 =
                   let uu____3530 =
                     let uu____3531 = un_uinst head1  in
                     uu____3531.FStar_Syntax_Syntax.n  in
                   let uu____3534 =
                     let uu____3535 = un_uinst head2  in
                     uu____3535.FStar_Syntax_Syntax.n  in
                   (uu____3530, uu____3534)  in
                 (match uu____3525 with
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
                  | uu____3562 -> FStar_Pervasives_Native.None))
         in
      let t12 = unmeta t11  in
      let t22 = unmeta t21  in
      match ((t12.FStar_Syntax_Syntax.n), (t22.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3580,uu____3581) ->
          let uu____3582 = unlazy t12  in eq_tm uu____3582 t22
      | (uu____3583,FStar_Syntax_Syntax.Tm_lazy uu____3584) ->
          let uu____3585 = unlazy t22  in eq_tm t12 uu____3585
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          let uu____3588 = FStar_Syntax_Syntax.bv_eq a b  in
          equal_if uu____3588
      | uu____3590 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3614 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3614
            (fun uu____3662  ->
               match uu____3662 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3677 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3677
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3691 = eq_tm f g  in
          eq_and uu____3691
            (fun uu____3694  ->
               let uu____3695 = eq_univs_list us vs  in equal_if uu____3695)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3697),uu____3698) -> Unknown
      | (uu____3699,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3700)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3703 = FStar_Const.eq_const c d  in equal_iff uu____3703
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3706)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3708))) ->
          let uu____3737 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3737
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3791 =
            let uu____3796 =
              let uu____3797 = un_uinst h1  in
              uu____3797.FStar_Syntax_Syntax.n  in
            let uu____3800 =
              let uu____3801 = un_uinst h2  in
              uu____3801.FStar_Syntax_Syntax.n  in
            (uu____3796, uu____3800)  in
          (match uu____3791 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3807 =
                    let uu____3809 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3809  in
                  FStar_List.mem uu____3807 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3811 ->
               let uu____3816 = eq_tm h1 h2  in
               eq_and uu____3816 (fun uu____3818  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t13,bs1),FStar_Syntax_Syntax.Tm_match
         (t23,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3924 = FStar_List.zip bs1 bs2  in
            let uu____3987 = eq_tm t13 t23  in
            FStar_List.fold_right
              (fun uu____4024  ->
                 fun a  ->
                   match uu____4024 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4117  -> branch_matches b1 b2))
              uu____3924 uu____3987
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v) ->
          let uu____4122 = eq_univs u v  in equal_if uu____4122
      | (FStar_Syntax_Syntax.Tm_quoted (t13,q1),FStar_Syntax_Syntax.Tm_quoted
         (t23,q2)) ->
          let uu____4136 = eq_quoteinfo q1 q2  in
          eq_and uu____4136 (fun uu____4138  -> eq_tm t13 t23)
      | (FStar_Syntax_Syntax.Tm_refine
         (t13,phi1),FStar_Syntax_Syntax.Tm_refine (t23,phi2)) ->
          let uu____4151 =
            eq_tm t13.FStar_Syntax_Syntax.sort t23.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4151 (fun uu____4153  -> eq_tm phi1 phi2)
      | uu____4154 -> Unknown

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
      | ([],uu____4226) -> NotEqual
      | (uu____4257,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          let uu____4346 =
            let uu____4348 = FStar_Syntax_Syntax.bv_eq x1 x2  in
            Prims.op_Negation uu____4348  in
          if uu____4346
          then NotEqual
          else
            (let uu____4353 = eq_tm t1 t2  in
             match uu____4353 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4354 = eq_antiquotes a11 a21  in
                 (match uu____4354 with
                  | NotEqual  -> NotEqual
                  | uu____4355 -> Unknown)
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
        | (uu____4439,uu____4440) -> false  in
      let uu____4450 = b1  in
      match uu____4450 with
      | (p1,w1,t1) ->
          let uu____4484 = b2  in
          (match uu____4484 with
           | (p2,w2,t2) ->
               let uu____4518 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4518
               then
                 let uu____4521 =
                   (let uu____4525 = eq_tm t1 t2  in uu____4525 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4534 = eq_tm t11 t21  in
                             uu____4534 = Equal) w1 w2)
                    in
                 (if uu____4521 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4599)::a11,(b,uu____4602)::b1) ->
          let uu____4676 = eq_tm a b  in
          (match uu____4676 with
           | Equal  -> eq_args a11 b1
           | uu____4677 -> Unknown)
      | uu____4678 -> Unknown

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
      | (FStar_Pervasives_Native.None ,uu____4733) -> NotEqual
      | (uu____4740,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4770 -> NotEqual
  
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4787) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4793,uu____4794) ->
        unrefine t2
    | uu____4835 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4843 =
      let uu____4844 = FStar_Syntax_Subst.compress t  in
      uu____4844.FStar_Syntax_Syntax.n  in
    match uu____4843 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4848 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4863) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4868 ->
        let uu____4885 =
          let uu____4886 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4886 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4885 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4949,uu____4950) ->
        is_uvar t1
    | uu____4991 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5000 =
      let uu____5001 = unrefine t  in uu____5001.FStar_Syntax_Syntax.n  in
    match uu____5000 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head,uu____5007) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5033) -> is_unit t1
    | uu____5038 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5047 =
      let uu____5048 = FStar_Syntax_Subst.compress t  in
      uu____5048.FStar_Syntax_Syntax.n  in
    match uu____5047 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5053 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5062 =
      let uu____5063 = FStar_Syntax_Subst.compress e  in
      uu____5063.FStar_Syntax_Syntax.n  in
    match uu____5062 with
    | FStar_Syntax_Syntax.Tm_abs uu____5067 -> true
    | uu____5087 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5096 =
      let uu____5097 = FStar_Syntax_Subst.compress t  in
      uu____5097.FStar_Syntax_Syntax.n  in
    match uu____5096 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5101 -> true
    | uu____5117 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5127) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5133,uu____5134) ->
        pre_typ t2
    | uu____5175 -> t1
  
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
      let uu____5200 =
        let uu____5201 = un_uinst typ1  in uu____5201.FStar_Syntax_Syntax.n
         in
      match uu____5200 with
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let head1 = un_uinst head  in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5266 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5296 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5317,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5324) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5329,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5340,uu____5341,uu____5342,uu____5343,uu____5344) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5354,uu____5355,uu____5356,uu____5357) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5363,uu____5364,uu____5365,uu____5366,uu____5367) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5375,uu____5376) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5378,uu____5379) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5381 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5382 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5383 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5396 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5420 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5446  ->
    match uu___7_5446 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'uuuuuu5460 'uuuuuu5461 .
    ('uuuuuu5460 FStar_Syntax_Syntax.syntax * 'uuuuuu5461) ->
      FStar_Range.range
  =
  fun uu____5472  ->
    match uu____5472 with | (hd,uu____5480) -> hd.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'uuuuuu5494 'uuuuuu5495 .
    ('uuuuuu5494 FStar_Syntax_Syntax.syntax * 'uuuuuu5495) Prims.list ->
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
      | uu____5593 ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args)) r
  
let (mk_app_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun bs  ->
      let uu____5652 =
        FStar_List.map
          (fun uu____5679  ->
             match uu____5679 with
             | (bv,aq) ->
                 let uu____5698 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5698, aq)) bs
         in
      mk_app f uu____5652
  
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
          (let uu____5749 =
             let uu____5755 =
               let uu____5757 =
                 let uu____5759 = FStar_Ident.ident_of_lid lid  in
                 FStar_Ident.text_of_id uu____5759  in
               mk_field_projector_name_from_string uu____5757 itext  in
             let uu____5760 = FStar_Ident.range_of_id i  in
             (uu____5755, uu____5760)  in
           FStar_Ident.mk_ident uu____5749)
         in
      let uu____5762 =
        let uu____5763 = FStar_Ident.ns_of_lid lid  in
        FStar_List.append uu____5763 [newi]  in
      FStar_Ident.lid_of_ids uu____5762
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5785 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5785
          then
            let uu____5788 =
              let uu____5794 =
                let uu____5796 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5796  in
              let uu____5799 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5794, uu____5799)  in
            FStar_Ident.mk_ident uu____5788
          else x.FStar_Syntax_Syntax.ppname  in
        mk_field_projector_name_from_ident lid nm
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5814) -> ses
    | uu____5823 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5838 = FStar_Syntax_Unionfind.find uv  in
      match uu____5838 with
      | FStar_Pervasives_Native.Some uu____5841 ->
          let uu____5842 =
            let uu____5844 =
              let uu____5846 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5846  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5844  in
          failwith uu____5842
      | uu____5851 -> FStar_Syntax_Unionfind.change uv t
  
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
            (let uu____5875 = FStar_Ident.text_of_id l1b  in
             let uu____5877 = FStar_Ident.text_of_id l2b  in
             uu____5875 = uu____5877)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5906 = FStar_Ident.text_of_id x1  in
                      let uu____5908 = FStar_Ident.text_of_id x2  in
                      uu____5906 = uu____5908) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5917 = FStar_Ident.text_of_id x1  in
                    let uu____5919 = FStar_Ident.text_of_id x2  in
                    uu____5917 = uu____5919) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5948 = FStar_Ident.text_of_id x1  in
                      let uu____5950 = FStar_Ident.text_of_id x2  in
                      uu____5948 = uu____5950) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5959 = FStar_Ident.text_of_id x1  in
                    let uu____5961 = FStar_Ident.text_of_id x2  in
                    uu____5959 = uu____5961) f1 f2)
      | uu____5964 -> q1 = q2
  
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
              let uu____6010 =
                let uu___1008_6011 = rc  in
                let uu____6012 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1008_6011.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6012;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1008_6011.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6010
           in
        match bs with
        | [] -> t
        | uu____6029 ->
            let body =
              let uu____6031 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6031  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6061 =
                   let uu____6062 =
                     let uu____6081 =
                       let uu____6090 = FStar_Syntax_Subst.close_binders bs
                          in
                       FStar_List.append uu____6090 bs'  in
                     let uu____6105 = close_lopt lopt'  in
                     (uu____6081, t1, uu____6105)  in
                   FStar_Syntax_Syntax.Tm_abs uu____6062  in
                 FStar_Syntax_Syntax.mk uu____6061 t1.FStar_Syntax_Syntax.pos
             | uu____6120 ->
                 let uu____6121 =
                   let uu____6122 =
                     let uu____6141 = FStar_Syntax_Subst.close_binders bs  in
                     let uu____6150 = close_lopt lopt  in
                     (uu____6141, body, uu____6150)  in
                   FStar_Syntax_Syntax.Tm_abs uu____6122  in
                 FStar_Syntax_Syntax.mk uu____6121 t.FStar_Syntax_Syntax.pos)
  
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
      | uu____6206 ->
          let uu____6215 =
            let uu____6216 =
              let uu____6231 = FStar_Syntax_Subst.close_binders bs  in
              let uu____6240 = FStar_Syntax_Subst.close_comp bs c  in
              (uu____6231, uu____6240)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6216  in
          FStar_Syntax_Syntax.mk uu____6215 c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6289 =
        let uu____6290 = FStar_Syntax_Subst.compress t  in
        uu____6290.FStar_Syntax_Syntax.n  in
      match uu____6289 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6320) ->
               let uu____6329 =
                 let uu____6330 = FStar_Syntax_Subst.compress tres  in
                 uu____6330.FStar_Syntax_Syntax.n  in
               (match uu____6329 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      t.FStar_Syntax_Syntax.pos
                | uu____6373 -> t)
           | uu____6374 -> t)
      | uu____6375 -> t
  
let rec (canon_arrow :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____6388 =
      let uu____6389 = FStar_Syntax_Subst.compress t  in
      uu____6389.FStar_Syntax_Syntax.n  in
    match uu____6388 with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let cn =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Total (t1,u) ->
              let uu____6427 =
                let uu____6436 = canon_arrow t1  in (uu____6436, u)  in
              FStar_Syntax_Syntax.Total uu____6427
          | uu____6443 -> c.FStar_Syntax_Syntax.n  in
        let c1 =
          let uu___1052_6447 = c  in
          {
            FStar_Syntax_Syntax.n = cn;
            FStar_Syntax_Syntax.pos =
              (uu___1052_6447.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___1052_6447.FStar_Syntax_Syntax.vars)
          }  in
        flat_arrow bs c1
    | uu____6450 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6468 =
        let uu____6469 =
          let uu____6476 =
            let uu____6479 =
              let uu____6480 = FStar_Syntax_Syntax.mk_binder b  in
              [uu____6480]  in
            FStar_Syntax_Subst.close uu____6479 t  in
          (b, uu____6476)  in
        FStar_Syntax_Syntax.Tm_refine uu____6469  in
      let uu____6501 =
        let uu____6502 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6502 t.FStar_Syntax_Syntax.pos  in
      FStar_Syntax_Syntax.mk uu____6468 uu____6501
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let (has_decreases : FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____6518 =
          FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
            (FStar_Util.find_opt
               (fun uu___8_6527  ->
                  match uu___8_6527 with
                  | FStar_Syntax_Syntax.DECREASES uu____6529 -> true
                  | uu____6533 -> false))
           in
        (match uu____6518 with
         | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES d) ->
             true
         | uu____6540 -> false)
    | uu____6544 -> false
  
let rec (arrow_formals_comp_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____6599 =
          (is_total_comp c) &&
            (let uu____6602 = has_decreases c  in
             Prims.op_Negation uu____6602)
           in
        if uu____6599
        then
          let uu____6617 = arrow_formals_comp_ln (comp_result c)  in
          (match uu____6617 with
           | (bs',k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6684;
           FStar_Syntax_Syntax.index = uu____6685;
           FStar_Syntax_Syntax.sort = s;_},uu____6687)
        ->
        let rec aux s1 k2 =
          let uu____6718 =
            let uu____6719 = FStar_Syntax_Subst.compress s1  in
            uu____6719.FStar_Syntax_Syntax.n  in
          match uu____6718 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6734 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6749;
                 FStar_Syntax_Syntax.index = uu____6750;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6752)
              -> aux s2 k2
          | uu____6760 ->
              let uu____6761 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6761)
           in
        aux s k1
    | uu____6776 ->
        let uu____6777 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6777)
  
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let uu____6802 = arrow_formals_comp_ln k  in
    match uu____6802 with | (bs,c) -> FStar_Syntax_Subst.open_comp bs c
  
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6857 = arrow_formals_comp_ln k  in
    match uu____6857 with | (bs,c) -> (bs, (comp_result c))
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6924 = arrow_formals_comp k  in
    match uu____6924 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7026 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7026 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____7050 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___9_7059  ->
                         match uu___9_7059 with
                         | FStar_Syntax_Syntax.DECREASES uu____7061 -> true
                         | uu____7065 -> false))
                  in
               (match uu____7050 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7100 ->
                    let uu____7103 = is_total_comp c1  in
                    if uu____7103
                    then
                      let uu____7122 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7122 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7215;
             FStar_Syntax_Syntax.index = uu____7216;
             FStar_Syntax_Syntax.sort = k2;_},uu____7218)
          -> arrow_until_decreases k2
      | uu____7226 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7247 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7247 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7301 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7322 =
                 FStar_Common.tabulate n_univs (fun uu____7328  -> false)  in
               let uu____7331 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7356  ->
                         match uu____7356 with
                         | (x,uu____7365) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7322 uu____7331)
           in
        ((n_univs + (FStar_List.length bs)), uu____7301)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7421 =
            let uu___1162_7422 = rc  in
            let uu____7423 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1162_7422.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7423;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1162_7422.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7421
      | uu____7432 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7466 =
        let uu____7467 =
          let uu____7470 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7470  in
        uu____7467.FStar_Syntax_Syntax.n  in
      match uu____7466 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7516 = aux t2 what  in
          (match uu____7516 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7588 -> ([], t1, abs_body_lcomp)  in
    let uu____7605 = aux t FStar_Pervasives_Native.None  in
    match uu____7605 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7653 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7653 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let no_acc uu____7687 =
      match uu____7687 with
      | (b,aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true )) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7701 -> aq  in
          (b, aq1)
       in
    let uu____7706 = arrow_formals_comp_ln t  in
    match uu____7706 with
    | (bs,c) ->
        (match bs with
         | [] -> t
         | uu____7743 ->
             let uu____7752 =
               let uu____7753 =
                 let uu____7768 = FStar_List.map no_acc bs  in
                 (uu____7768, c)  in
               FStar_Syntax_Syntax.Tm_arrow uu____7753  in
             FStar_Syntax_Syntax.mk uu____7752 t.FStar_Syntax_Syntax.pos)
  
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
                    | (FStar_Pervasives_Native.None ,uu____7939) -> def
                    | (uu____7950,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7962) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu____7978  ->
                                  FStar_Syntax_Syntax.U_name uu____7978))
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
            let uu____8060 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____8060 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____8095 ->
            let t' = arrow binders c  in
            let uu____8107 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____8107 with
             | (uvs1,t'1) ->
                 let uu____8128 =
                   let uu____8129 = FStar_Syntax_Subst.compress t'1  in
                   uu____8129.FStar_Syntax_Syntax.n  in
                 (match uu____8128 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8178 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8203 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Parser_Const.is_tuple_constructor_string uu____8203
    | uu____8205 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8216 -> false
  
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
      let uu____8279 =
        let uu____8280 = pre_typ t  in uu____8280.FStar_Syntax_Syntax.n  in
      match uu____8279 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8285 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8299 =
        let uu____8300 = pre_typ t  in uu____8300.FStar_Syntax_Syntax.n  in
      match uu____8299 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8304 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8306) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8332) ->
          is_constructed_typ t1 lid
      | uu____8337 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8350 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8351 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8352 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8354) -> get_tycon t2
    | uu____8379 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8387 =
      let uu____8388 = un_uinst t  in uu____8388.FStar_Syntax_Syntax.n  in
    match uu____8387 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8393 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8407 =
        let uu____8411 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8411  in
      match uu____8407 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8443 -> false
    else false
  
let (ktype : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Range.dummyRange
  
let (ktype0 : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Range.dummyRange
  
let (type_u :
  unit -> (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe)) =
  fun uu____8462  ->
    let u =
      let uu____8468 =
        FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
      FStar_All.pipe_left
        (fun uu____8489  -> FStar_Syntax_Syntax.U_unif uu____8489) uu____8468
       in
    let uu____8490 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Range.dummyRange
       in
    (uu____8490, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8503 = eq_tm a a'  in
      match uu____8503 with | Equal  -> true | uu____8506 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8511 =
    let uu____8512 =
      let uu____8513 =
        FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
          FStar_Range.dummyRange
         in
      FStar_Syntax_Syntax.lid_as_fv uu____8513
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Syntax.Tm_fvar uu____8512  in
  FStar_Syntax_Syntax.mk uu____8511 FStar_Range.dummyRange 
let (exp_true_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Range.dummyRange
  
let (exp_false_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Range.dummyRange
  
let (exp_unit : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    FStar_Range.dummyRange
  
let (exp_int : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_int (s, FStar_Pervasives_Native.None)))
      FStar_Range.dummyRange
  
let (exp_char : FStar_BaseTypes.char -> FStar_Syntax_Syntax.term) =
  fun c  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c))
      FStar_Range.dummyRange
  
let (exp_string : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (s, FStar_Range.dummyRange)))
      FStar_Range.dummyRange
  
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
          let uu____8626 =
            let uu____8629 =
              let uu____8630 =
                let uu____8647 =
                  let uu____8658 = FStar_Syntax_Syntax.as_arg phi11  in
                  let uu____8667 =
                    let uu____8678 = FStar_Syntax_Syntax.as_arg phi2  in
                    [uu____8678]  in
                  uu____8658 :: uu____8667  in
                (tand, uu____8647)  in
              FStar_Syntax_Syntax.Tm_app uu____8630  in
            let uu____8723 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            FStar_Syntax_Syntax.mk uu____8629 uu____8723  in
          FStar_Pervasives_Native.Some uu____8626
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8756 =
          let uu____8757 =
            let uu____8774 =
              let uu____8785 = FStar_Syntax_Syntax.as_arg phi1  in
              let uu____8794 =
                let uu____8805 = FStar_Syntax_Syntax.as_arg phi2  in
                [uu____8805]  in
              uu____8785 :: uu____8794  in
            (op_t, uu____8774)  in
          FStar_Syntax_Syntax.Tm_app uu____8757  in
        let uu____8850 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Syntax.mk uu____8756 uu____8850
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8863 =
      let uu____8864 =
        let uu____8881 =
          let uu____8892 = FStar_Syntax_Syntax.as_arg phi  in [uu____8892]
           in
        (t_not, uu____8881)  in
      FStar_Syntax_Syntax.Tm_app uu____8864  in
    FStar_Syntax_Syntax.mk uu____8863 phi.FStar_Syntax_Syntax.pos
  
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
    let uu____9089 =
      let uu____9090 =
        let uu____9107 =
          let uu____9118 = FStar_Syntax_Syntax.as_arg e  in [uu____9118]  in
        (b2t_v, uu____9107)  in
      FStar_Syntax_Syntax.Tm_app uu____9090  in
    FStar_Syntax_Syntax.mk uu____9089 e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9165 = head_and_args e  in
    match uu____9165 with
    | (hd,args) ->
        let uu____9210 =
          let uu____9225 =
            let uu____9226 = FStar_Syntax_Subst.compress hd  in
            uu____9226.FStar_Syntax_Syntax.n  in
          (uu____9225, args)  in
        (match uu____9210 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9243)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9278 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9300 =
      let uu____9301 = unmeta t  in uu____9301.FStar_Syntax_Syntax.n  in
    match uu____9300 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9306 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9329 = is_t_true t1  in
      if uu____9329
      then t2
      else
        (let uu____9336 = is_t_true t2  in
         if uu____9336 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9364 = is_t_true t1  in
      if uu____9364
      then t_true
      else
        (let uu____9371 = is_t_true t2  in
         if uu____9371 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9400 =
        let uu____9401 =
          let uu____9418 =
            let uu____9429 = FStar_Syntax_Syntax.as_arg e1  in
            let uu____9438 =
              let uu____9449 = FStar_Syntax_Syntax.as_arg e2  in [uu____9449]
               in
            uu____9429 :: uu____9438  in
          (teq, uu____9418)  in
        FStar_Syntax_Syntax.Tm_app uu____9401  in
      let uu____9494 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      FStar_Syntax_Syntax.mk uu____9400 uu____9494
  
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
          let uu____9517 =
            let uu____9518 =
              let uu____9535 =
                let uu____9546 = FStar_Syntax_Syntax.iarg t  in
                let uu____9555 =
                  let uu____9566 = FStar_Syntax_Syntax.as_arg e1  in
                  let uu____9575 =
                    let uu____9586 = FStar_Syntax_Syntax.as_arg e2  in
                    [uu____9586]  in
                  uu____9566 :: uu____9575  in
                uu____9546 :: uu____9555  in
              (eq_inst, uu____9535)  in
            FStar_Syntax_Syntax.Tm_app uu____9518  in
          let uu____9639 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          FStar_Syntax_Syntax.mk uu____9517 uu____9639
  
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
            FStar_Range.dummyRange
           in
        let uu____9664 =
          let uu____9665 =
            let uu____9682 =
              let uu____9693 = FStar_Syntax_Syntax.iarg t  in
              let uu____9702 =
                let uu____9713 = FStar_Syntax_Syntax.as_arg x  in
                let uu____9722 =
                  let uu____9733 = FStar_Syntax_Syntax.as_arg t'  in
                  [uu____9733]  in
                uu____9713 :: uu____9722  in
              uu____9693 :: uu____9702  in
            (t_has_type1, uu____9682)  in
          FStar_Syntax_Syntax.Tm_app uu____9665  in
        FStar_Syntax_Syntax.mk uu____9664 FStar_Range.dummyRange
  
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
            FStar_Range.dummyRange
           in
        let uu____9810 =
          let uu____9811 =
            let uu____9828 =
              let uu____9839 = FStar_Syntax_Syntax.iarg t  in
              let uu____9848 =
                let uu____9859 = FStar_Syntax_Syntax.as_arg e  in
                [uu____9859]  in
              uu____9839 :: uu____9848  in
            (t_with_type1, uu____9828)  in
          FStar_Syntax_Syntax.Tm_app uu____9811  in
        FStar_Syntax_Syntax.mk uu____9810 FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9906 =
    let uu____9907 =
      let uu____9914 =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
          FStar_Syntax_Syntax.delta_constant
          (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
         in
      (uu____9914, [FStar_Syntax_Syntax.U_zero])  in
    FStar_Syntax_Syntax.Tm_uinst uu____9907  in
  FStar_Syntax_Syntax.mk uu____9906 FStar_Range.dummyRange 
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
        let uu____9997 =
          let uu____9998 =
            let uu____10015 =
              let uu____10026 =
                FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
              let uu____10035 =
                let uu____10046 =
                  let uu____10055 =
                    let uu____10056 =
                      let uu____10057 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____10057]  in
                    abs uu____10056 body
                      (FStar_Pervasives_Native.Some (residual_tot ktype0))
                     in
                  FStar_Syntax_Syntax.as_arg uu____10055  in
                [uu____10046]  in
              uu____10026 :: uu____10035  in
            (fa, uu____10015)  in
          FStar_Syntax_Syntax.Tm_app uu____9998  in
        FStar_Syntax_Syntax.mk uu____9997 FStar_Range.dummyRange
  
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
             let uu____10184 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10184
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10203 -> true
    | uu____10205 -> false
  
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
          let uu____10252 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10252, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10281 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10281, FStar_Pervasives_Native.None, t2)  in
        let uu____10295 =
          let uu____10296 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10296  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          uu____10295
  
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
      let uu____10372 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10375 =
        let uu____10386 = FStar_Syntax_Syntax.as_arg p  in [uu____10386]  in
      mk_app uu____10372 uu____10375
  
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
      let uu____10426 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10429 =
        let uu____10440 = FStar_Syntax_Syntax.as_arg p  in [uu____10440]  in
      mk_app uu____10426 uu____10429
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10475 = head_and_args t  in
    match uu____10475 with
    | (head,args) ->
        let head1 = unascribe head  in
        let head2 = un_uinst head1  in
        let uu____10524 =
          let uu____10539 =
            let uu____10540 = FStar_Syntax_Subst.compress head2  in
            uu____10540.FStar_Syntax_Syntax.n  in
          (uu____10539, args)  in
        (match uu____10524 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10559)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10625 =
                    let uu____10630 =
                      let uu____10631 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10631]  in
                    FStar_Syntax_Subst.open_term uu____10630 p  in
                  (match uu____10625 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10688 -> failwith "impossible"  in
                       let uu____10696 =
                         let uu____10698 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10698
                          in
                       if uu____10696
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10714 -> FStar_Pervasives_Native.None)
         | uu____10717 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10748 = head_and_args t  in
    match uu____10748 with
    | (head,args) ->
        let uu____10799 =
          let uu____10814 =
            let uu____10815 = FStar_Syntax_Subst.compress head  in
            uu____10815.FStar_Syntax_Syntax.n  in
          (uu____10814, args)  in
        (match uu____10799 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10837;
               FStar_Syntax_Syntax.vars = uu____10838;_},u::[]),(t1,uu____10841)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10888 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10923 = head_and_args t  in
    match uu____10923 with
    | (head,args) ->
        let uu____10974 =
          let uu____10989 =
            let uu____10990 = FStar_Syntax_Subst.compress head  in
            uu____10990.FStar_Syntax_Syntax.n  in
          (uu____10989, args)  in
        (match uu____10974 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____11012;
               FStar_Syntax_Syntax.vars = uu____11013;_},u::[]),(t1,uu____11016)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11063 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11091 =
      let uu____11108 = unmeta t  in head_and_args uu____11108  in
    match uu____11091 with
    | (head,uu____11111) ->
        let uu____11136 =
          let uu____11137 = un_uinst head  in
          uu____11137.FStar_Syntax_Syntax.n  in
        (match uu____11136 with
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
         | uu____11142 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11162 =
      let uu____11163 = FStar_Syntax_Subst.compress t  in
      uu____11163.FStar_Syntax_Syntax.n  in
    match uu____11162 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11269 =
          let uu____11274 =
            let uu____11275 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11275  in
          (b, uu____11274)  in
        FStar_Pervasives_Native.Some uu____11269
    | uu____11280 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11303 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11303
      (fun uu____11331  ->
         match uu____11331 with
         | (b,c) ->
             let uu____11350 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11350 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11413 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11450 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11450
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11502 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11545 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11586 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11972) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11984) ->
          unmeta_monadic t
      | uu____11997 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12066 =
        match uu____12066 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12104  ->
                   match uu____12104 with
                   | (lid,out_lid) ->
                       let uu____12113 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12113
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12140 = head_and_args t  in
      match uu____12140 with
      | (hd,args) ->
          let uu____12185 =
            let uu____12186 = un_uinst hd  in
            uu____12186.FStar_Syntax_Syntax.n  in
          (match uu____12185 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12192 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12201 = un_squash t  in
      FStar_Util.bind_opt uu____12201
        (fun t1  ->
           let uu____12217 = head_and_args' t1  in
           match uu____12217 with
           | (hd,args) ->
               let uu____12256 =
                 let uu____12257 = un_uinst hd  in
                 uu____12257.FStar_Syntax_Syntax.n  in
               (match uu____12256 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12263 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12304,pats)) ->
          let uu____12342 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12342)
      | uu____12355 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12422 = head_and_args t1  in
        match uu____12422 with
        | (t2,args) ->
            let uu____12477 = un_uinst t2  in
            let uu____12478 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12519  ->
                      match uu____12519 with
                      | (t3,imp) ->
                          let uu____12538 = unascribe t3  in
                          (uu____12538, imp)))
               in
            (uu____12477, uu____12478)
         in
      let rec aux qopt out t1 =
        let uu____12589 = let uu____12613 = flat t1  in (qopt, uu____12613)
           in
        match uu____12589 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12653;
                 FStar_Syntax_Syntax.vars = uu____12654;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12657);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12658;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12659;_},uu____12660)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12762;
                 FStar_Syntax_Syntax.vars = uu____12763;_},uu____12764::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12767);
                  FStar_Syntax_Syntax.pos = uu____12768;
                  FStar_Syntax_Syntax.vars = uu____12769;_},uu____12770)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12887;
               FStar_Syntax_Syntax.vars = uu____12888;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12891);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12892;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12893;_},uu____12894)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12987 =
              let uu____12991 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12991  in
            aux uu____12987 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13001;
               FStar_Syntax_Syntax.vars = uu____13002;_},uu____13003::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____13006);
                FStar_Syntax_Syntax.pos = uu____13007;
                FStar_Syntax_Syntax.vars = uu____13008;_},uu____13009)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13118 =
              let uu____13122 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13122  in
            aux uu____13118 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13132) ->
            let bs = FStar_List.rev out  in
            let uu____13185 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13185 with
             | (bs1,t2) ->
                 let uu____13194 = patterns t2  in
                 (match uu____13194 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13244 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13299 = un_squash t  in
      FStar_Util.bind_opt uu____13299
        (fun t1  ->
           let uu____13314 = arrow_one t1  in
           match uu____13314 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13329 =
                 let uu____13331 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13331  in
               if uu____13329
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13341 = comp_to_comp_typ_nouniv c  in
                    uu____13341.FStar_Syntax_Syntax.result_typ  in
                  let uu____13342 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13342
                  then
                    let uu____13349 = patterns q  in
                    match uu____13349 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13412 =
                       let uu____13413 =
                         let uu____13418 =
                           let uu____13419 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13430 =
                             let uu____13441 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13441]  in
                           uu____13419 :: uu____13430  in
                         (FStar_Parser_Const.imp_lid, uu____13418)  in
                       BaseConn uu____13413  in
                     FStar_Pervasives_Native.Some uu____13412))
           | uu____13474 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13482 = un_squash t  in
      FStar_Util.bind_opt uu____13482
        (fun t1  ->
           let uu____13513 = head_and_args' t1  in
           match uu____13513 with
           | (hd,args) ->
               let uu____13552 =
                 let uu____13567 =
                   let uu____13568 = un_uinst hd  in
                   uu____13568.FStar_Syntax_Syntax.n  in
                 (uu____13567, args)  in
               (match uu____13552 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13585)::(a2,uu____13587)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13638 =
                      let uu____13639 = FStar_Syntax_Subst.compress a2  in
                      uu____13639.FStar_Syntax_Syntax.n  in
                    (match uu____13638 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13646) ->
                         let uu____13681 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13681 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13734 -> failwith "impossible"  in
                              let uu____13742 = patterns q1  in
                              (match uu____13742 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13803 -> FStar_Pervasives_Native.None)
                | uu____13804 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13827 = destruct_sq_forall phi  in
          (match uu____13827 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13837  ->
                    FStar_Pervasives_Native.Some uu____13837)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13844 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13850 = destruct_sq_exists phi  in
          (match uu____13850 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13860  ->
                    FStar_Pervasives_Native.Some uu____13860)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13867 -> f1)
      | uu____13870 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13874 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13874
      (fun uu____13879  ->
         let uu____13880 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13880
           (fun uu____13885  ->
              let uu____13886 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13886
                (fun uu____13891  ->
                   let uu____13892 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13892
                     (fun uu____13897  ->
                        let uu____13898 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13898
                          (fun uu____13902  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13920 =
            let uu____13925 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13925  in
          let uu____13926 =
            let uu____13927 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13927  in
          let uu____13930 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13920 a.FStar_Syntax_Syntax.action_univs uu____13926
            FStar_Parser_Const.effect_Tot_lid uu____13930 [] pos
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
        t.FStar_Syntax_Syntax.pos
       in
    let uu____13956 =
      let uu____13957 =
        let uu____13974 =
          let uu____13985 = FStar_Syntax_Syntax.as_arg t  in [uu____13985]
           in
        (reify_, uu____13974)  in
      FStar_Syntax_Syntax.Tm_app uu____13957  in
    FStar_Syntax_Syntax.mk uu____13956 t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14037 =
        let uu____14038 =
          let uu____14039 = FStar_Ident.lid_of_str "Bogus.Effect"  in
          FStar_Const.Const_reflect uu____14039  in
        FStar_Syntax_Syntax.Tm_constant uu____14038  in
      FStar_Syntax_Syntax.mk uu____14037 t.FStar_Syntax_Syntax.pos  in
    let uu____14041 =
      let uu____14042 =
        let uu____14059 =
          let uu____14070 = FStar_Syntax_Syntax.as_arg t  in [uu____14070]
           in
        (reflect_, uu____14059)  in
      FStar_Syntax_Syntax.Tm_app uu____14042  in
    FStar_Syntax_Syntax.mk uu____14041 t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14114 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14131 = unfold_lazy i  in delta_qualifier uu____14131
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14133 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14134 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14135 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14158 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14171 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14172 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14179 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14180 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14196) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14201;
           FStar_Syntax_Syntax.index = uu____14202;
           FStar_Syntax_Syntax.sort = t2;_},uu____14204)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14213) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14219,uu____14220) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14262) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14287,t2,uu____14289) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14314,t2) -> delta_qualifier t2
  
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
    let uu____14353 = delta_qualifier t  in incr_delta_depth uu____14353
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14361 =
      let uu____14362 = FStar_Syntax_Subst.compress t  in
      uu____14362.FStar_Syntax_Syntax.n  in
    match uu____14361 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14367 -> false
  
let rec apply_last :
  'uuuuuu14376 .
    ('uuuuuu14376 -> 'uuuuuu14376) ->
      'uuuuuu14376 Prims.list -> 'uuuuuu14376 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14402 = f a  in [uu____14402]
      | x::xs -> let uu____14407 = apply_last f xs  in x :: uu____14407
  
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
          let uu____14462 =
            let uu____14463 =
              FStar_Syntax_Syntax.lid_as_fv l1
                FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.Tm_fvar uu____14463  in
          FStar_Syntax_Syntax.mk uu____14462 rng  in
        let cons args pos =
          let uu____14475 =
            let uu____14476 = ctor FStar_Parser_Const.cons_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____14476
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____14475 args pos  in
        let nil args pos =
          let uu____14488 =
            let uu____14489 = ctor FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____14489
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____14488 args pos  in
        let uu____14490 =
          let uu____14491 =
            let uu____14492 = FStar_Syntax_Syntax.iarg typ  in [uu____14492]
             in
          nil uu____14491 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14526 =
                 let uu____14527 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14536 =
                   let uu____14547 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14556 =
                     let uu____14567 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14567]  in
                   uu____14547 :: uu____14556  in
                 uu____14527 :: uu____14536  in
               cons uu____14526 t.FStar_Syntax_Syntax.pos) l uu____14490
  
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
        | uu____14676 -> false
  
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
          | uu____14790 -> false
  
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
        | uu____14956 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____14994 = FStar_ST.op_Bang debug_term_eq  in
          if uu____14994
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
        let t11 = let uu____15196 = unmeta_safe t1  in canon_app uu____15196
           in
        let t21 = let uu____15200 = unmeta_safe t2  in canon_app uu____15200
           in
        let uu____15203 =
          let uu____15208 =
            let uu____15209 =
              let uu____15212 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15212  in
            uu____15209.FStar_Syntax_Syntax.n  in
          let uu____15213 =
            let uu____15214 =
              let uu____15217 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15217  in
            uu____15214.FStar_Syntax_Syntax.n  in
          (uu____15208, uu____15213)  in
        match uu____15203 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15219,uu____15220) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15229,FStar_Syntax_Syntax.Tm_uinst uu____15230) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15239,uu____15240) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15257,FStar_Syntax_Syntax.Tm_delayed uu____15258) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15275,uu____15276) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15305,FStar_Syntax_Syntax.Tm_ascribed uu____15306) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15345 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15345
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15350 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15350
        | (FStar_Syntax_Syntax.Tm_type
           uu____15353,FStar_Syntax_Syntax.Tm_type uu____15354) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15412 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15412) &&
              (let uu____15422 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15422)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15471 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15471) &&
              (let uu____15481 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15481)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15498 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15498) &&
              (let uu____15502 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15502)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15559 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15559) &&
              (let uu____15563 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15563)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15652 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15652) &&
              (let uu____15656 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15656)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15673,uu____15674) ->
            let uu____15675 =
              let uu____15677 = unlazy t11  in
              term_eq_dbg dbg uu____15677 t21  in
            check "lazy_l" uu____15675
        | (uu____15679,FStar_Syntax_Syntax.Tm_lazy uu____15680) ->
            let uu____15681 =
              let uu____15683 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15683  in
            check "lazy_r" uu____15681
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15728 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15728))
              &&
              (let uu____15732 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15732)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15736),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15738)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15798 =
               let uu____15800 = eq_quoteinfo qi1 qi2  in uu____15800 = Equal
                in
             check "tm_quoted qi" uu____15798) &&
              (let uu____15803 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15803)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15833 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15833) &&
                   (let uu____15837 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15837)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15856 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15856) &&
                    (let uu____15860 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15860))
                   &&
                   (let uu____15864 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15864)
             | uu____15867 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15873) -> fail "unk"
        | (uu____15875,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15877,uu____15878) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15880,uu____15881) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15883,uu____15884) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15886,uu____15887) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15889,uu____15890) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15892,uu____15893) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15913,uu____15914) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15930,uu____15931) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15939,uu____15940) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15958,uu____15959) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____15983,uu____15984) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____15999,uu____16000) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16014,uu____16015) ->
            fail "bottom"
        | (uu____16023,FStar_Syntax_Syntax.Tm_bvar uu____16024) ->
            fail "bottom"
        | (uu____16026,FStar_Syntax_Syntax.Tm_name uu____16027) ->
            fail "bottom"
        | (uu____16029,FStar_Syntax_Syntax.Tm_fvar uu____16030) ->
            fail "bottom"
        | (uu____16032,FStar_Syntax_Syntax.Tm_constant uu____16033) ->
            fail "bottom"
        | (uu____16035,FStar_Syntax_Syntax.Tm_type uu____16036) ->
            fail "bottom"
        | (uu____16038,FStar_Syntax_Syntax.Tm_abs uu____16039) ->
            fail "bottom"
        | (uu____16059,FStar_Syntax_Syntax.Tm_arrow uu____16060) ->
            fail "bottom"
        | (uu____16076,FStar_Syntax_Syntax.Tm_refine uu____16077) ->
            fail "bottom"
        | (uu____16085,FStar_Syntax_Syntax.Tm_app uu____16086) ->
            fail "bottom"
        | (uu____16104,FStar_Syntax_Syntax.Tm_match uu____16105) ->
            fail "bottom"
        | (uu____16129,FStar_Syntax_Syntax.Tm_let uu____16130) ->
            fail "bottom"
        | (uu____16145,FStar_Syntax_Syntax.Tm_uvar uu____16146) ->
            fail "bottom"
        | (uu____16160,FStar_Syntax_Syntax.Tm_meta uu____16161) ->
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
               let uu____16196 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16196)
          (fun q1  ->
             fun q2  ->
               let uu____16208 =
                 let uu____16210 = eq_aqual q1 q2  in uu____16210 = Equal  in
               check "arg qual" uu____16208) a1 a2

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
               let uu____16235 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16235)
          (fun q1  ->
             fun q2  ->
               let uu____16247 =
                 let uu____16249 = eq_aqual q1 q2  in uu____16249 = Equal  in
               check "binder qual" uu____16247) b1 b2

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
        ((let uu____16263 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16263) &&
           (let uu____16267 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16267))
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
    fun uu____16277  ->
      fun uu____16278  ->
        match (uu____16277, uu____16278) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16405 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16405) &&
               (let uu____16409 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16409))
              &&
              (let uu____16413 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16455 -> false  in
               check "branch when" uu____16413)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16476 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16476) &&
           (let uu____16485 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16485))
          &&
          (let uu____16489 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16489)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16506 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16506 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16560 ->
        let uu____16575 =
          let uu____16577 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16577  in
        Prims.int_one + uu____16575
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16580 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16580
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16584 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16584
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16593 = sizeof t1  in (FStar_List.length us) + uu____16593
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16597) ->
        let uu____16622 = sizeof t1  in
        let uu____16624 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16639  ->
                 match uu____16639 with
                 | (bv,uu____16649) ->
                     let uu____16654 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16654) Prims.int_zero bs
           in
        uu____16622 + uu____16624
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____16683 = sizeof hd  in
        let uu____16685 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16700  ->
                 match uu____16700 with
                 | (arg,uu____16710) ->
                     let uu____16715 = sizeof arg  in acc + uu____16715)
            Prims.int_zero args
           in
        uu____16683 + uu____16685
    | uu____16718 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16732 =
        let uu____16733 = un_uinst t  in uu____16733.FStar_Syntax_Syntax.n
         in
      match uu____16732 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16738 -> false
  
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
           let uu____16799 = head_and_args t  in
           match uu____16799 with
           | (head,args) ->
               let uu____16854 =
                 let uu____16855 = FStar_Syntax_Subst.compress head  in
                 uu____16855.FStar_Syntax_Syntax.n  in
               (match uu____16854 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16881 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____16914 = is_fvar attr a  in Prims.op_Negation uu____16914)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      FStar_Errors.set_option_warning_callback_range
        (FStar_Pervasives_Native.Some r);
      (let set_options s =
         let uu____16936 = FStar_Options.set_options s  in
         match uu____16936 with
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
           ((let uu____16950 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____16950 (fun uu____16952  -> ()));
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
           let uu____16966 = FStar_Options.internal_pop ()  in
           if uu____16966
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
    | FStar_Syntax_Syntax.Tm_delayed uu____16998 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17017 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17032 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17033 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17034 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17043) ->
        let uu____17068 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17068 with
         | (bs1,t2) ->
             let uu____17077 =
               FStar_List.collect
                 (fun uu____17089  ->
                    match uu____17089 with
                    | (b,uu____17099) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17104 = unbound_variables t2  in
             FStar_List.append uu____17077 uu____17104)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17129 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17129 with
         | (bs1,c1) ->
             let uu____17138 =
               FStar_List.collect
                 (fun uu____17150  ->
                    match uu____17150 with
                    | (b,uu____17160) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17165 = unbound_variables_comp c1  in
             FStar_List.append uu____17138 uu____17165)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17174 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17174 with
         | (bs,t2) ->
             let uu____17197 =
               FStar_List.collect
                 (fun uu____17209  ->
                    match uu____17209 with
                    | (b1,uu____17219) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17224 = unbound_variables t2  in
             FStar_List.append uu____17197 uu____17224)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17253 =
          FStar_List.collect
            (fun uu____17267  ->
               match uu____17267 with
               | (x,uu____17279) -> unbound_variables x) args
           in
        let uu____17288 = unbound_variables t1  in
        FStar_List.append uu____17253 uu____17288
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17329 = unbound_variables t1  in
        let uu____17332 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17347 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17347 with
                  | (p,wopt,t2) ->
                      let uu____17369 = unbound_variables t2  in
                      let uu____17372 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17369 uu____17372))
           in
        FStar_List.append uu____17329 uu____17332
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17386) ->
        let uu____17427 = unbound_variables t1  in
        let uu____17430 =
          let uu____17433 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17464 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17433 uu____17464  in
        FStar_List.append uu____17427 uu____17430
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17505 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17508 =
          let uu____17511 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17514 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17519 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17521 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17521 with
                 | (uu____17542,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17511 uu____17514  in
        FStar_List.append uu____17505 uu____17508
    | FStar_Syntax_Syntax.Tm_let ((uu____17544,lbs),t1) ->
        let uu____17564 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17564 with
         | (lbs1,t2) ->
             let uu____17579 = unbound_variables t2  in
             let uu____17582 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17589 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17592 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17589 uu____17592) lbs1
                in
             FStar_List.append uu____17579 uu____17582)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17609 = unbound_variables t1  in
        let uu____17612 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17617,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17672  ->
                      match uu____17672 with
                      | (a,uu____17684) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17693,uu____17694,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17700,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17706 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17715 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17716 -> []  in
        FStar_List.append uu____17609 uu____17612

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17723) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17733) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17743 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17746 =
          FStar_List.collect
            (fun uu____17760  ->
               match uu____17760 with
               | (a,uu____17772) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17743 uu____17746

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
            let uu____17887 = head_and_args h  in
            (match uu____17887 with
             | (head,args) ->
                 let uu____17948 =
                   let uu____17949 = FStar_Syntax_Subst.compress head  in
                   uu____17949.FStar_Syntax_Syntax.n  in
                 (match uu____17948 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18002 -> aux (h :: acc) t))
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
      let uu____18026 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18026 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2518_18068 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2518_18068.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2518_18068.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2518_18068.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2518_18068.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2518_18068.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18076 =
      let uu____18077 = FStar_Syntax_Subst.compress t  in
      uu____18077.FStar_Syntax_Syntax.n  in
    match uu____18076 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18081,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18109)::uu____18110 ->
                  let pats' = unmeta pats  in
                  let uu____18170 = head_and_args pats'  in
                  (match uu____18170 with
                   | (head,uu____18189) ->
                       let uu____18214 =
                         let uu____18215 = un_uinst head  in
                         uu____18215.FStar_Syntax_Syntax.n  in
                       (match uu____18214 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18220 -> false))
              | uu____18222 -> false)
         | uu____18234 -> false)
    | uu____18236 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18252 =
      let uu____18269 = unmeta e  in head_and_args uu____18269  in
    match uu____18252 with
    | (head,args) ->
        let uu____18300 =
          let uu____18315 =
            let uu____18316 = un_uinst head  in
            uu____18316.FStar_Syntax_Syntax.n  in
          (uu____18315, args)  in
        (match uu____18300 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18334) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18358::(hd,uu____18360)::(tl,uu____18362)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18429 =
               let uu____18432 =
                 let uu____18435 = list_elements tl  in
                 FStar_Util.must uu____18435  in
               hd :: uu____18432  in
             FStar_Pervasives_Native.Some uu____18429
         | uu____18444 -> FStar_Pervasives_Native.None)
  
let (unthunk : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____18467 =
      let uu____18468 = FStar_Syntax_Subst.compress t  in
      uu____18468.FStar_Syntax_Syntax.n  in
    match uu____18467 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18473) ->
        let uu____18508 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18508 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18540 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18540
             then
               let uu____18545 =
                 let uu____18556 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18556]  in
               mk_app t uu____18545
             else e1)
    | uu____18583 ->
        let uu____18584 =
          let uu____18595 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18595]  in
        mk_app t uu____18584
  
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
        let uu____18656 = list_elements e  in
        match uu____18656 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18691 =
          let uu____18708 = unmeta p  in
          FStar_All.pipe_right uu____18708 head_and_args  in
        match uu____18691 with
        | (head,args) ->
            let uu____18759 =
              let uu____18774 =
                let uu____18775 = un_uinst head  in
                uu____18775.FStar_Syntax_Syntax.n  in
              (uu____18774, args)  in
            (match uu____18759 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18797,uu____18798)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18850 ->
                 let uu____18865 =
                   let uu____18871 =
                     let uu____18873 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18873
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____18871)  in
                 FStar_Errors.raise_error uu____18865
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____18916 =
            let uu____18933 = unmeta t1  in
            FStar_All.pipe_right uu____18933 head_and_args  in
          match uu____18916 with
          | (head,args) ->
              let uu____18980 =
                let uu____18995 =
                  let uu____18996 = un_uinst head  in
                  uu____18996.FStar_Syntax_Syntax.n  in
                (uu____18995, args)  in
              (match uu____18980 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19015)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19052 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19082 = smt_pat_or t1  in
            (match uu____19082 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19104 = list_elements1 e  in
                 FStar_All.pipe_right uu____19104
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19134 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19134
                           (FStar_List.map one_pat)))
             | uu____19163 ->
                 let uu____19168 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19168])
        | uu____19223 ->
            let uu____19226 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19226]
         in
      let uu____19281 =
        let uu____19312 =
          let uu____19313 = FStar_Syntax_Subst.compress t  in
          uu____19313.FStar_Syntax_Syntax.n  in
        match uu____19312 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19368 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19368 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19435;
                        FStar_Syntax_Syntax.effect_name = uu____19436;
                        FStar_Syntax_Syntax.result_typ = uu____19437;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19439)::(post,uu____19441)::(pats,uu____19443)::[];
                        FStar_Syntax_Syntax.flags = uu____19444;_}
                      ->
                      let uu____19505 = lemma_pats pats  in
                      (binders1, pre, post, uu____19505)
                  | uu____19540 -> failwith "impos"))
        | uu____19572 -> failwith "Impos"  in
      match uu____19281 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19656 =
              let uu____19657 =
                let uu____19664 = mk_imp pre post1  in
                let uu____19667 =
                  let uu____19668 =
                    let uu____19689 =
                      FStar_Syntax_Syntax.binders_to_names binders  in
                    (uu____19689, patterns)  in
                  FStar_Syntax_Syntax.Meta_pattern uu____19668  in
                (uu____19664, uu____19667)  in
              FStar_Syntax_Syntax.Tm_meta uu____19657  in
            FStar_Syntax_Syntax.mk uu____19656 t.FStar_Syntax_Syntax.pos  in
          let quant =
            let uu____19713 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19713 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19743 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19754 -> true
    | uu____19756 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19767 -> true
    | uu____19769 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19787 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19788 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19789 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19790 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19791 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19792 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19793 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19794 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19797 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19800 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19787;
        FStar_Syntax_Syntax.bind_wp = uu____19788;
        FStar_Syntax_Syntax.stronger = uu____19789;
        FStar_Syntax_Syntax.if_then_else = uu____19790;
        FStar_Syntax_Syntax.ite_wp = uu____19791;
        FStar_Syntax_Syntax.close_wp = uu____19792;
        FStar_Syntax_Syntax.trivial = uu____19793;
        FStar_Syntax_Syntax.repr = uu____19794;
        FStar_Syntax_Syntax.return_repr = uu____19797;
        FStar_Syntax_Syntax.bind_repr = uu____19800
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____19832 =
        match uu____19832 with
        | (ts1,ts2) ->
            let uu____19843 = f ts1  in
            let uu____19844 = f ts2  in (uu____19843, uu____19844)
         in
      let uu____19845 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____19850 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____19855 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____19860 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____19865 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____19845;
        FStar_Syntax_Syntax.l_return = uu____19850;
        FStar_Syntax_Syntax.l_bind = uu____19855;
        FStar_Syntax_Syntax.l_subcomp = uu____19860;
        FStar_Syntax_Syntax.l_if_then_else = uu____19865
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
          let uu____19887 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____19887
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19889 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____19889
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19891 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____19891
  
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
    | uu____19906 -> FStar_Pervasives_Native.None
  
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
        let uu____19920 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19920
          (fun uu____19927  -> FStar_Pervasives_Native.Some uu____19927)
  
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
        let uu____19967 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19967
          (fun uu____19974  -> FStar_Pervasives_Native.Some uu____19974)
  
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
        let uu____19988 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19988
          (fun uu____19995  -> FStar_Pervasives_Native.Some uu____19995)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20009  -> FStar_Pervasives_Native.Some uu____20009)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20013  -> FStar_Pervasives_Native.Some uu____20013)
    | uu____20014 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20026 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20026
          (fun uu____20033  -> FStar_Pervasives_Native.Some uu____20033)
    | uu____20034 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20048  -> FStar_Pervasives_Native.Some uu____20048)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20052  -> FStar_Pervasives_Native.Some uu____20052)
    | uu____20053 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20067  -> FStar_Pervasives_Native.Some uu____20067)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20071  -> FStar_Pervasives_Native.Some uu____20071)
    | uu____20072 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20096 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20097 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20099 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20099
          (fun uu____20106  -> FStar_Pervasives_Native.Some uu____20106)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun uu____20120  -> FStar_Pervasives_Native.Some uu____20120)
    | uu____20121 -> FStar_Pervasives_Native.None
  