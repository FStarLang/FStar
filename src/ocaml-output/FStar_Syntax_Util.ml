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
                  FStar_Ident.string_of_id uu____105  in
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
        FStar_Ident.string_of_id uu____120  in
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
            let uu____1266 = FStar_Ident.string_of_id u11  in
            let uu____1268 = FStar_Ident.string_of_id u21  in
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
      let uu___238_1603 = c  in
      let uu____1604 =
        let uu____1605 =
          let uu___240_1606 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___240_1606.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___240_1606.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___240_1606.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___240_1606.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1605  in
      {
        FStar_Syntax_Syntax.n = uu____1604;
        FStar_Syntax_Syntax.pos = (uu___238_1603.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___238_1603.FStar_Syntax_Syntax.vars)
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
            (let uu___379_2500 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___379_2500.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___379_2500.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___379_2500.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___379_2500.FStar_Syntax_Syntax.flags)
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
         (FStar_Syntax_Syntax.Arg_qualifier_meta_tac
         t1)),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t2))) -> eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
         t1)),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t2))) -> eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4780 -> NotEqual
  
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4797) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4803,uu____4804) ->
        unrefine t2
    | uu____4845 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4853 =
      let uu____4854 = FStar_Syntax_Subst.compress t  in
      uu____4854.FStar_Syntax_Syntax.n  in
    match uu____4853 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4858 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4873) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4878 ->
        let uu____4895 =
          let uu____4896 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4896 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4895 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4959,uu____4960) ->
        is_uvar t1
    | uu____5001 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5010 =
      let uu____5011 = unrefine t  in uu____5011.FStar_Syntax_Syntax.n  in
    match uu____5010 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head,uu____5017) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5043) -> is_unit t1
    | uu____5048 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5057 =
      let uu____5058 = FStar_Syntax_Subst.compress t  in
      uu____5058.FStar_Syntax_Syntax.n  in
    match uu____5057 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5063 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5072 =
      let uu____5073 = FStar_Syntax_Subst.compress e  in
      uu____5073.FStar_Syntax_Syntax.n  in
    match uu____5072 with
    | FStar_Syntax_Syntax.Tm_abs uu____5077 -> true
    | uu____5097 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5106 =
      let uu____5107 = FStar_Syntax_Subst.compress t  in
      uu____5107.FStar_Syntax_Syntax.n  in
    match uu____5106 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5111 -> true
    | uu____5127 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5137) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5143,uu____5144) ->
        pre_typ t2
    | uu____5185 -> t1
  
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
      let uu____5210 =
        let uu____5211 = un_uinst typ1  in uu____5211.FStar_Syntax_Syntax.n
         in
      match uu____5210 with
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let head1 = un_uinst head  in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5276 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5306 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5327,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5334) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5339,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5350,uu____5351,uu____5352,uu____5353,uu____5354) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5364,uu____5365,uu____5366,uu____5367) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5373,uu____5374,uu____5375,uu____5376,uu____5377) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5385,uu____5386) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5388,uu____5389) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5391 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5392 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5393 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5406 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5430 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5456  ->
    match uu___7_5456 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'uuuuuu5470 'uuuuuu5471 .
    ('uuuuuu5470 FStar_Syntax_Syntax.syntax * 'uuuuuu5471) ->
      FStar_Range.range
  =
  fun uu____5482  ->
    match uu____5482 with | (hd,uu____5490) -> hd.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'uuuuuu5504 'uuuuuu5505 .
    ('uuuuuu5504 FStar_Syntax_Syntax.syntax * 'uuuuuu5505) Prims.list ->
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
      | uu____5603 ->
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
      let uu____5662 =
        FStar_List.map
          (fun uu____5689  ->
             match uu____5689 with
             | (bv,aq) ->
                 let uu____5708 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5708, aq)) bs
         in
      mk_app f uu____5662
  
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
      let itext = FStar_Ident.string_of_id i  in
      let newi =
        if field_projector_contains_constructor itext
        then i
        else
          (let uu____5759 =
             let uu____5765 =
               let uu____5767 =
                 let uu____5769 = FStar_Ident.ident_of_lid lid  in
                 FStar_Ident.string_of_id uu____5769  in
               mk_field_projector_name_from_string uu____5767 itext  in
             let uu____5770 = FStar_Ident.range_of_id i  in
             (uu____5765, uu____5770)  in
           FStar_Ident.mk_ident uu____5759)
         in
      let uu____5772 =
        let uu____5773 = FStar_Ident.ns_of_lid lid  in
        FStar_List.append uu____5773 [newi]  in
      FStar_Ident.lid_of_ids uu____5772
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5795 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5795
          then
            let uu____5798 =
              let uu____5804 =
                let uu____5806 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5806  in
              let uu____5809 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5804, uu____5809)  in
            FStar_Ident.mk_ident uu____5798
          else x.FStar_Syntax_Syntax.ppname  in
        mk_field_projector_name_from_ident lid nm
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5824) -> ses
    | uu____5833 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5848 = FStar_Syntax_Unionfind.find uv  in
      match uu____5848 with
      | FStar_Pervasives_Native.Some uu____5851 ->
          let uu____5852 =
            let uu____5854 =
              let uu____5856 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5856  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5854  in
          failwith uu____5852
      | uu____5861 -> FStar_Syntax_Unionfind.change uv t
  
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
            (let uu____5885 = FStar_Ident.string_of_id l1b  in
             let uu____5887 = FStar_Ident.string_of_id l2b  in
             uu____5885 = uu____5887)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5916 = FStar_Ident.string_of_id x1  in
                      let uu____5918 = FStar_Ident.string_of_id x2  in
                      uu____5916 = uu____5918) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5927 = FStar_Ident.string_of_id x1  in
                    let uu____5929 = FStar_Ident.string_of_id x2  in
                    uu____5927 = uu____5929) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5958 = FStar_Ident.string_of_id x1  in
                      let uu____5960 = FStar_Ident.string_of_id x2  in
                      uu____5958 = uu____5960) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5969 = FStar_Ident.string_of_id x1  in
                    let uu____5971 = FStar_Ident.string_of_id x2  in
                    uu____5969 = uu____5971) f1 f2)
      | uu____5974 -> q1 = q2
  
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
              let uu____6020 =
                let uu___1018_6021 = rc  in
                let uu____6022 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1018_6021.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6022;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1018_6021.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6020
           in
        match bs with
        | [] -> t
        | uu____6039 ->
            let body =
              let uu____6041 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6041  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6071 =
                   let uu____6072 =
                     let uu____6091 =
                       let uu____6100 = FStar_Syntax_Subst.close_binders bs
                          in
                       FStar_List.append uu____6100 bs'  in
                     let uu____6115 = close_lopt lopt'  in
                     (uu____6091, t1, uu____6115)  in
                   FStar_Syntax_Syntax.Tm_abs uu____6072  in
                 FStar_Syntax_Syntax.mk uu____6071 t1.FStar_Syntax_Syntax.pos
             | uu____6130 ->
                 let uu____6131 =
                   let uu____6132 =
                     let uu____6151 = FStar_Syntax_Subst.close_binders bs  in
                     let uu____6160 = close_lopt lopt  in
                     (uu____6151, body, uu____6160)  in
                   FStar_Syntax_Syntax.Tm_abs uu____6132  in
                 FStar_Syntax_Syntax.mk uu____6131 t.FStar_Syntax_Syntax.pos)
  
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
      | uu____6216 ->
          let uu____6225 =
            let uu____6226 =
              let uu____6241 = FStar_Syntax_Subst.close_binders bs  in
              let uu____6250 = FStar_Syntax_Subst.close_comp bs c  in
              (uu____6241, uu____6250)  in
            FStar_Syntax_Syntax.Tm_arrow uu____6226  in
          FStar_Syntax_Syntax.mk uu____6225 c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6299 =
        let uu____6300 = FStar_Syntax_Subst.compress t  in
        uu____6300.FStar_Syntax_Syntax.n  in
      match uu____6299 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6330) ->
               let uu____6339 =
                 let uu____6340 = FStar_Syntax_Subst.compress tres  in
                 uu____6340.FStar_Syntax_Syntax.n  in
               (match uu____6339 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      t.FStar_Syntax_Syntax.pos
                | uu____6383 -> t)
           | uu____6384 -> t)
      | uu____6385 -> t
  
let rec (canon_arrow :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____6398 =
      let uu____6399 = FStar_Syntax_Subst.compress t  in
      uu____6399.FStar_Syntax_Syntax.n  in
    match uu____6398 with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let cn =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Total (t1,u) ->
              let uu____6437 =
                let uu____6446 = canon_arrow t1  in (uu____6446, u)  in
              FStar_Syntax_Syntax.Total uu____6437
          | uu____6453 -> c.FStar_Syntax_Syntax.n  in
        let c1 =
          let uu___1062_6457 = c  in
          {
            FStar_Syntax_Syntax.n = cn;
            FStar_Syntax_Syntax.pos =
              (uu___1062_6457.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___1062_6457.FStar_Syntax_Syntax.vars)
          }  in
        flat_arrow bs c1
    | uu____6460 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6478 =
        let uu____6479 =
          let uu____6486 =
            let uu____6489 =
              let uu____6490 = FStar_Syntax_Syntax.mk_binder b  in
              [uu____6490]  in
            FStar_Syntax_Subst.close uu____6489 t  in
          (b, uu____6486)  in
        FStar_Syntax_Syntax.Tm_refine uu____6479  in
      let uu____6511 =
        let uu____6512 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6512 t.FStar_Syntax_Syntax.pos  in
      FStar_Syntax_Syntax.mk uu____6478 uu____6511
  
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
        let uu____6572 = is_total_comp c  in
        if uu____6572
        then
          let uu____6587 = arrow_formals_comp_ln (comp_result c)  in
          (match uu____6587 with
           | (bs',k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6654;
           FStar_Syntax_Syntax.index = uu____6655;
           FStar_Syntax_Syntax.sort = s;_},uu____6657)
        ->
        let rec aux s1 k2 =
          let uu____6688 =
            let uu____6689 = FStar_Syntax_Subst.compress s1  in
            uu____6689.FStar_Syntax_Syntax.n  in
          match uu____6688 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6704 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6719;
                 FStar_Syntax_Syntax.index = uu____6720;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6722)
              -> aux s2 k2
          | uu____6730 ->
              let uu____6731 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6731)
           in
        aux s k1
    | uu____6746 ->
        let uu____6747 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6747)
  
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let uu____6772 = arrow_formals_comp_ln k  in
    match uu____6772 with | (bs,c) -> FStar_Syntax_Subst.open_comp bs c
  
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6827 = arrow_formals_comp_ln k  in
    match uu____6827 with | (bs,c) -> (bs, (comp_result c))
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6894 = arrow_formals_comp k  in
    match uu____6894 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6996 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6996 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____7020 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_7029  ->
                         match uu___8_7029 with
                         | FStar_Syntax_Syntax.DECREASES uu____7031 -> true
                         | uu____7035 -> false))
                  in
               (match uu____7020 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7070 ->
                    let uu____7073 = is_total_comp c1  in
                    if uu____7073
                    then
                      let uu____7092 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7092 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7185;
             FStar_Syntax_Syntax.index = uu____7186;
             FStar_Syntax_Syntax.sort = k2;_},uu____7188)
          -> arrow_until_decreases k2
      | uu____7196 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7217 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7217 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7271 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7292 =
                 FStar_Common.tabulate n_univs (fun uu____7298  -> false)  in
               let uu____7301 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7326  ->
                         match uu____7326 with
                         | (x,uu____7335) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7292 uu____7301)
           in
        ((n_univs + (FStar_List.length bs)), uu____7271)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7391 =
            let uu___1160_7392 = rc  in
            let uu____7393 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1160_7392.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7393;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1160_7392.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7391
      | uu____7402 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7436 =
        let uu____7437 =
          let uu____7440 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7440  in
        uu____7437.FStar_Syntax_Syntax.n  in
      match uu____7436 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7486 = aux t2 what  in
          (match uu____7486 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7558 -> ([], t1, abs_body_lcomp)  in
    let uu____7575 = aux t FStar_Pervasives_Native.None  in
    match uu____7575 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7623 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7623 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let no_acc uu____7657 =
      match uu____7657 with
      | (b,aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true )) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7671 -> aq  in
          (b, aq1)
       in
    let uu____7676 = arrow_formals_comp_ln t  in
    match uu____7676 with
    | (bs,c) ->
        (match bs with
         | [] -> t
         | uu____7713 ->
             let uu____7722 =
               let uu____7723 =
                 let uu____7738 = FStar_List.map no_acc bs  in
                 (uu____7738, c)  in
               FStar_Syntax_Syntax.Tm_arrow uu____7723  in
             FStar_Syntax_Syntax.mk uu____7722 t.FStar_Syntax_Syntax.pos)
  
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
                    | (FStar_Pervasives_Native.None ,uu____7909) -> def
                    | (uu____7920,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7932) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu____7948  ->
                                  FStar_Syntax_Syntax.U_name uu____7948))
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
            let uu____8030 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____8030 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____8065 ->
            let t' = arrow binders c  in
            let uu____8077 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____8077 with
             | (uvs1,t'1) ->
                 let uu____8098 =
                   let uu____8099 = FStar_Syntax_Subst.compress t'1  in
                   uu____8099.FStar_Syntax_Syntax.n  in
                 (match uu____8098 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8148 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8173 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Parser_Const.is_tuple_constructor_string uu____8173
    | uu____8175 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8186 -> false
  
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
      let uu____8249 =
        let uu____8250 = pre_typ t  in uu____8250.FStar_Syntax_Syntax.n  in
      match uu____8249 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8255 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8269 =
        let uu____8270 = pre_typ t  in uu____8270.FStar_Syntax_Syntax.n  in
      match uu____8269 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8274 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8276) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8302) ->
          is_constructed_typ t1 lid
      | uu____8307 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8320 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8321 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8322 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8324) -> get_tycon t2
    | uu____8349 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8357 =
      let uu____8358 = un_uinst t  in uu____8358.FStar_Syntax_Syntax.n  in
    match uu____8357 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8363 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8377 =
        let uu____8381 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8381  in
      match uu____8377 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8413 -> false
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
  fun uu____8432  ->
    let u =
      let uu____8438 =
        FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
      FStar_All.pipe_left
        (fun uu____8459  -> FStar_Syntax_Syntax.U_unif uu____8459) uu____8438
       in
    let uu____8460 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Range.dummyRange
       in
    (uu____8460, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8473 = eq_tm a a'  in
      match uu____8473 with | Equal  -> true | uu____8476 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8481 =
    let uu____8482 =
      let uu____8483 =
        FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
          FStar_Range.dummyRange
         in
      FStar_Syntax_Syntax.lid_as_fv uu____8483
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Syntax.Tm_fvar uu____8482  in
  FStar_Syntax_Syntax.mk uu____8481 FStar_Range.dummyRange 
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
          let uu____8596 =
            let uu____8599 =
              let uu____8600 =
                let uu____8617 =
                  let uu____8628 = FStar_Syntax_Syntax.as_arg phi11  in
                  let uu____8637 =
                    let uu____8648 = FStar_Syntax_Syntax.as_arg phi2  in
                    [uu____8648]  in
                  uu____8628 :: uu____8637  in
                (tand, uu____8617)  in
              FStar_Syntax_Syntax.Tm_app uu____8600  in
            let uu____8693 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            FStar_Syntax_Syntax.mk uu____8599 uu____8693  in
          FStar_Pervasives_Native.Some uu____8596
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8726 =
          let uu____8727 =
            let uu____8744 =
              let uu____8755 = FStar_Syntax_Syntax.as_arg phi1  in
              let uu____8764 =
                let uu____8775 = FStar_Syntax_Syntax.as_arg phi2  in
                [uu____8775]  in
              uu____8755 :: uu____8764  in
            (op_t, uu____8744)  in
          FStar_Syntax_Syntax.Tm_app uu____8727  in
        let uu____8820 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Syntax.mk uu____8726 uu____8820
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8833 =
      let uu____8834 =
        let uu____8851 =
          let uu____8862 = FStar_Syntax_Syntax.as_arg phi  in [uu____8862]
           in
        (t_not, uu____8851)  in
      FStar_Syntax_Syntax.Tm_app uu____8834  in
    FStar_Syntax_Syntax.mk uu____8833 phi.FStar_Syntax_Syntax.pos
  
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
    let uu____9059 =
      let uu____9060 =
        let uu____9077 =
          let uu____9088 = FStar_Syntax_Syntax.as_arg e  in [uu____9088]  in
        (b2t_v, uu____9077)  in
      FStar_Syntax_Syntax.Tm_app uu____9060  in
    FStar_Syntax_Syntax.mk uu____9059 e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9135 = head_and_args e  in
    match uu____9135 with
    | (hd,args) ->
        let uu____9180 =
          let uu____9195 =
            let uu____9196 = FStar_Syntax_Subst.compress hd  in
            uu____9196.FStar_Syntax_Syntax.n  in
          (uu____9195, args)  in
        (match uu____9180 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9213)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9248 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9270 =
      let uu____9271 = unmeta t  in uu____9271.FStar_Syntax_Syntax.n  in
    match uu____9270 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9276 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9299 = is_t_true t1  in
      if uu____9299
      then t2
      else
        (let uu____9306 = is_t_true t2  in
         if uu____9306 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9334 = is_t_true t1  in
      if uu____9334
      then t_true
      else
        (let uu____9341 = is_t_true t2  in
         if uu____9341 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9370 =
        let uu____9371 =
          let uu____9388 =
            let uu____9399 = FStar_Syntax_Syntax.as_arg e1  in
            let uu____9408 =
              let uu____9419 = FStar_Syntax_Syntax.as_arg e2  in [uu____9419]
               in
            uu____9399 :: uu____9408  in
          (teq, uu____9388)  in
        FStar_Syntax_Syntax.Tm_app uu____9371  in
      let uu____9464 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      FStar_Syntax_Syntax.mk uu____9370 uu____9464
  
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
          let uu____9487 =
            let uu____9488 =
              let uu____9505 =
                let uu____9516 = FStar_Syntax_Syntax.iarg t  in
                let uu____9525 =
                  let uu____9536 = FStar_Syntax_Syntax.as_arg e1  in
                  let uu____9545 =
                    let uu____9556 = FStar_Syntax_Syntax.as_arg e2  in
                    [uu____9556]  in
                  uu____9536 :: uu____9545  in
                uu____9516 :: uu____9525  in
              (eq_inst, uu____9505)  in
            FStar_Syntax_Syntax.Tm_app uu____9488  in
          let uu____9609 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          FStar_Syntax_Syntax.mk uu____9487 uu____9609
  
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
        let uu____9634 =
          let uu____9635 =
            let uu____9652 =
              let uu____9663 = FStar_Syntax_Syntax.iarg t  in
              let uu____9672 =
                let uu____9683 = FStar_Syntax_Syntax.as_arg x  in
                let uu____9692 =
                  let uu____9703 = FStar_Syntax_Syntax.as_arg t'  in
                  [uu____9703]  in
                uu____9683 :: uu____9692  in
              uu____9663 :: uu____9672  in
            (t_has_type1, uu____9652)  in
          FStar_Syntax_Syntax.Tm_app uu____9635  in
        FStar_Syntax_Syntax.mk uu____9634 FStar_Range.dummyRange
  
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
        let uu____9780 =
          let uu____9781 =
            let uu____9798 =
              let uu____9809 = FStar_Syntax_Syntax.iarg t  in
              let uu____9818 =
                let uu____9829 = FStar_Syntax_Syntax.as_arg e  in
                [uu____9829]  in
              uu____9809 :: uu____9818  in
            (t_with_type1, uu____9798)  in
          FStar_Syntax_Syntax.Tm_app uu____9781  in
        FStar_Syntax_Syntax.mk uu____9780 FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9876 =
    let uu____9877 =
      let uu____9884 =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
          FStar_Syntax_Syntax.delta_constant
          (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
         in
      (uu____9884, [FStar_Syntax_Syntax.U_zero])  in
    FStar_Syntax_Syntax.Tm_uinst uu____9877  in
  FStar_Syntax_Syntax.mk uu____9876 FStar_Range.dummyRange 
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
        let uu____9967 =
          let uu____9968 =
            let uu____9985 =
              let uu____9996 =
                FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
              let uu____10005 =
                let uu____10016 =
                  let uu____10025 =
                    let uu____10026 =
                      let uu____10027 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____10027]  in
                    abs uu____10026 body
                      (FStar_Pervasives_Native.Some (residual_tot ktype0))
                     in
                  FStar_Syntax_Syntax.as_arg uu____10025  in
                [uu____10016]  in
              uu____9996 :: uu____10005  in
            (fa, uu____9985)  in
          FStar_Syntax_Syntax.Tm_app uu____9968  in
        FStar_Syntax_Syntax.mk uu____9967 FStar_Range.dummyRange
  
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
             let uu____10154 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10154
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10173 -> true
    | uu____10175 -> false
  
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
          let uu____10222 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10222, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10251 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10251, FStar_Pervasives_Native.None, t2)  in
        let uu____10265 =
          let uu____10266 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10266  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          uu____10265
  
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
      let uu____10342 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10345 =
        let uu____10356 = FStar_Syntax_Syntax.as_arg p  in [uu____10356]  in
      mk_app uu____10342 uu____10345
  
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
      let uu____10396 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10399 =
        let uu____10410 = FStar_Syntax_Syntax.as_arg p  in [uu____10410]  in
      mk_app uu____10396 uu____10399
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10445 = head_and_args t  in
    match uu____10445 with
    | (head,args) ->
        let head1 = unascribe head  in
        let head2 = un_uinst head1  in
        let uu____10494 =
          let uu____10509 =
            let uu____10510 = FStar_Syntax_Subst.compress head2  in
            uu____10510.FStar_Syntax_Syntax.n  in
          (uu____10509, args)  in
        (match uu____10494 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10529)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10595 =
                    let uu____10600 =
                      let uu____10601 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10601]  in
                    FStar_Syntax_Subst.open_term uu____10600 p  in
                  (match uu____10595 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10658 -> failwith "impossible"  in
                       let uu____10666 =
                         let uu____10668 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10668
                          in
                       if uu____10666
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10684 -> FStar_Pervasives_Native.None)
         | uu____10687 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10718 = head_and_args t  in
    match uu____10718 with
    | (head,args) ->
        let uu____10769 =
          let uu____10784 =
            let uu____10785 = FStar_Syntax_Subst.compress head  in
            uu____10785.FStar_Syntax_Syntax.n  in
          (uu____10784, args)  in
        (match uu____10769 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10807;
               FStar_Syntax_Syntax.vars = uu____10808;_},u::[]),(t1,uu____10811)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10858 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10893 = head_and_args t  in
    match uu____10893 with
    | (head,args) ->
        let uu____10944 =
          let uu____10959 =
            let uu____10960 = FStar_Syntax_Subst.compress head  in
            uu____10960.FStar_Syntax_Syntax.n  in
          (uu____10959, args)  in
        (match uu____10944 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10982;
               FStar_Syntax_Syntax.vars = uu____10983;_},u::[]),(t1,uu____10986)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11033 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11061 =
      let uu____11078 = unmeta t  in head_and_args uu____11078  in
    match uu____11061 with
    | (head,uu____11081) ->
        let uu____11106 =
          let uu____11107 = un_uinst head  in
          uu____11107.FStar_Syntax_Syntax.n  in
        (match uu____11106 with
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
         | uu____11112 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11132 =
      let uu____11133 = FStar_Syntax_Subst.compress t  in
      uu____11133.FStar_Syntax_Syntax.n  in
    match uu____11132 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11239 =
          let uu____11244 =
            let uu____11245 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11245  in
          (b, uu____11244)  in
        FStar_Pervasives_Native.Some uu____11239
    | uu____11250 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11273 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11273
      (fun uu____11301  ->
         match uu____11301 with
         | (b,c) ->
             let uu____11320 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11320 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11383 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11420 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11420
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11472 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11515 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11556 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11942) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11954) ->
          unmeta_monadic t
      | uu____11967 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12036 =
        match uu____12036 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12074  ->
                   match uu____12074 with
                   | (lid,out_lid) ->
                       let uu____12083 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12083
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12110 = head_and_args t  in
      match uu____12110 with
      | (hd,args) ->
          let uu____12155 =
            let uu____12156 = un_uinst hd  in
            uu____12156.FStar_Syntax_Syntax.n  in
          (match uu____12155 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12162 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12171 = un_squash t  in
      FStar_Util.bind_opt uu____12171
        (fun t1  ->
           let uu____12187 = head_and_args' t1  in
           match uu____12187 with
           | (hd,args) ->
               let uu____12226 =
                 let uu____12227 = un_uinst hd  in
                 uu____12227.FStar_Syntax_Syntax.n  in
               (match uu____12226 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12233 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12274,pats)) ->
          let uu____12312 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12312)
      | uu____12325 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12392 = head_and_args t1  in
        match uu____12392 with
        | (t2,args) ->
            let uu____12447 = un_uinst t2  in
            let uu____12448 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12489  ->
                      match uu____12489 with
                      | (t3,imp) ->
                          let uu____12508 = unascribe t3  in
                          (uu____12508, imp)))
               in
            (uu____12447, uu____12448)
         in
      let rec aux qopt out t1 =
        let uu____12559 = let uu____12583 = flat t1  in (qopt, uu____12583)
           in
        match uu____12559 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12623;
                 FStar_Syntax_Syntax.vars = uu____12624;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12627);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12628;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12629;_},uu____12630)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12732;
                 FStar_Syntax_Syntax.vars = uu____12733;_},uu____12734::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12737);
                  FStar_Syntax_Syntax.pos = uu____12738;
                  FStar_Syntax_Syntax.vars = uu____12739;_},uu____12740)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12857;
               FStar_Syntax_Syntax.vars = uu____12858;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12861);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12862;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12863;_},uu____12864)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12957 =
              let uu____12961 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12961  in
            aux uu____12957 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12971;
               FStar_Syntax_Syntax.vars = uu____12972;_},uu____12973::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12976);
                FStar_Syntax_Syntax.pos = uu____12977;
                FStar_Syntax_Syntax.vars = uu____12978;_},uu____12979)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13088 =
              let uu____13092 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13092  in
            aux uu____13088 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13102) ->
            let bs = FStar_List.rev out  in
            let uu____13155 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13155 with
             | (bs1,t2) ->
                 let uu____13164 = patterns t2  in
                 (match uu____13164 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13214 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13269 = un_squash t  in
      FStar_Util.bind_opt uu____13269
        (fun t1  ->
           let uu____13284 = arrow_one t1  in
           match uu____13284 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13299 =
                 let uu____13301 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13301  in
               if uu____13299
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13311 = comp_to_comp_typ_nouniv c  in
                    uu____13311.FStar_Syntax_Syntax.result_typ  in
                  let uu____13312 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13312
                  then
                    let uu____13319 = patterns q  in
                    match uu____13319 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13382 =
                       let uu____13383 =
                         let uu____13388 =
                           let uu____13389 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13400 =
                             let uu____13411 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13411]  in
                           uu____13389 :: uu____13400  in
                         (FStar_Parser_Const.imp_lid, uu____13388)  in
                       BaseConn uu____13383  in
                     FStar_Pervasives_Native.Some uu____13382))
           | uu____13444 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13452 = un_squash t  in
      FStar_Util.bind_opt uu____13452
        (fun t1  ->
           let uu____13483 = head_and_args' t1  in
           match uu____13483 with
           | (hd,args) ->
               let uu____13522 =
                 let uu____13537 =
                   let uu____13538 = un_uinst hd  in
                   uu____13538.FStar_Syntax_Syntax.n  in
                 (uu____13537, args)  in
               (match uu____13522 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13555)::(a2,uu____13557)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13608 =
                      let uu____13609 = FStar_Syntax_Subst.compress a2  in
                      uu____13609.FStar_Syntax_Syntax.n  in
                    (match uu____13608 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13616) ->
                         let uu____13651 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13651 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13704 -> failwith "impossible"  in
                              let uu____13712 = patterns q1  in
                              (match uu____13712 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13773 -> FStar_Pervasives_Native.None)
                | uu____13774 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13797 = destruct_sq_forall phi  in
          (match uu____13797 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13807  ->
                    FStar_Pervasives_Native.Some uu____13807)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13814 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13820 = destruct_sq_exists phi  in
          (match uu____13820 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13830  ->
                    FStar_Pervasives_Native.Some uu____13830)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13837 -> f1)
      | uu____13840 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13844 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13844
      (fun uu____13849  ->
         let uu____13850 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13850
           (fun uu____13855  ->
              let uu____13856 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13856
                (fun uu____13861  ->
                   let uu____13862 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13862
                     (fun uu____13867  ->
                        let uu____13868 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13868
                          (fun uu____13872  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13890 =
            let uu____13895 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13895  in
          let uu____13896 =
            let uu____13897 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13897  in
          let uu____13900 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13890 a.FStar_Syntax_Syntax.action_univs uu____13896
            FStar_Parser_Const.effect_Tot_lid uu____13900 [] pos
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
    let uu____13926 =
      let uu____13927 =
        let uu____13944 =
          let uu____13955 = FStar_Syntax_Syntax.as_arg t  in [uu____13955]
           in
        (reify_, uu____13944)  in
      FStar_Syntax_Syntax.Tm_app uu____13927  in
    FStar_Syntax_Syntax.mk uu____13926 t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14007 =
        let uu____14008 =
          let uu____14009 = FStar_Ident.lid_of_str "Bogus.Effect"  in
          FStar_Const.Const_reflect uu____14009  in
        FStar_Syntax_Syntax.Tm_constant uu____14008  in
      FStar_Syntax_Syntax.mk uu____14007 t.FStar_Syntax_Syntax.pos  in
    let uu____14011 =
      let uu____14012 =
        let uu____14029 =
          let uu____14040 = FStar_Syntax_Syntax.as_arg t  in [uu____14040]
           in
        (reflect_, uu____14029)  in
      FStar_Syntax_Syntax.Tm_app uu____14012  in
    FStar_Syntax_Syntax.mk uu____14011 t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14084 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14101 = unfold_lazy i  in delta_qualifier uu____14101
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14103 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14104 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14105 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14128 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14141 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14142 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14149 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14150 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14166) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14171;
           FStar_Syntax_Syntax.index = uu____14172;
           FStar_Syntax_Syntax.sort = t2;_},uu____14174)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14183) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14189,uu____14190) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14232) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14257,t2,uu____14259) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14284,t2) -> delta_qualifier t2
  
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
    let uu____14323 = delta_qualifier t  in incr_delta_depth uu____14323
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14331 =
      let uu____14332 = FStar_Syntax_Subst.compress t  in
      uu____14332.FStar_Syntax_Syntax.n  in
    match uu____14331 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14337 -> false
  
let rec apply_last :
  'uuuuuu14346 .
    ('uuuuuu14346 -> 'uuuuuu14346) ->
      'uuuuuu14346 Prims.list -> 'uuuuuu14346 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14372 = f a  in [uu____14372]
      | x::xs -> let uu____14377 = apply_last f xs  in x :: uu____14377
  
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
          let uu____14432 =
            let uu____14433 =
              FStar_Syntax_Syntax.lid_as_fv l1
                FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.Tm_fvar uu____14433  in
          FStar_Syntax_Syntax.mk uu____14432 rng  in
        let cons args pos =
          let uu____14445 =
            let uu____14446 = ctor FStar_Parser_Const.cons_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____14446
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____14445 args pos  in
        let nil args pos =
          let uu____14458 =
            let uu____14459 = ctor FStar_Parser_Const.nil_lid  in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____14459
              [FStar_Syntax_Syntax.U_zero]
             in
          FStar_Syntax_Syntax.mk_Tm_app uu____14458 args pos  in
        let uu____14460 =
          let uu____14461 =
            let uu____14462 = FStar_Syntax_Syntax.iarg typ  in [uu____14462]
             in
          nil uu____14461 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14496 =
                 let uu____14497 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14506 =
                   let uu____14517 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14526 =
                     let uu____14537 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14537]  in
                   uu____14517 :: uu____14526  in
                 uu____14497 :: uu____14506  in
               cons uu____14496 t.FStar_Syntax_Syntax.pos) l uu____14460
  
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
        | uu____14646 -> false
  
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
          | uu____14760 -> false
  
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
        | uu____14926 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____14964 = FStar_ST.op_Bang debug_term_eq  in
          if uu____14964
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
        let t11 = let uu____15152 = unmeta_safe t1  in canon_app uu____15152
           in
        let t21 = let uu____15156 = unmeta_safe t2  in canon_app uu____15156
           in
        let uu____15159 =
          let uu____15164 =
            let uu____15165 =
              let uu____15168 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15168  in
            uu____15165.FStar_Syntax_Syntax.n  in
          let uu____15169 =
            let uu____15170 =
              let uu____15173 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15173  in
            uu____15170.FStar_Syntax_Syntax.n  in
          (uu____15164, uu____15169)  in
        match uu____15159 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15175,uu____15176) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15185,FStar_Syntax_Syntax.Tm_uinst uu____15186) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15195,uu____15196) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15213,FStar_Syntax_Syntax.Tm_delayed uu____15214) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15231,uu____15232) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15261,FStar_Syntax_Syntax.Tm_ascribed uu____15262) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15301 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15301
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15306 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15306
        | (FStar_Syntax_Syntax.Tm_type
           uu____15309,FStar_Syntax_Syntax.Tm_type uu____15310) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15368 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15368) &&
              (let uu____15378 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15378)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15427 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15427) &&
              (let uu____15437 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15437)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15454 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15454) &&
              (let uu____15458 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15458)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15515 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15515) &&
              (let uu____15519 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15519)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15608 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15608) &&
              (let uu____15612 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15612)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15629,uu____15630) ->
            let uu____15631 =
              let uu____15633 = unlazy t11  in
              term_eq_dbg dbg uu____15633 t21  in
            check "lazy_l" uu____15631
        | (uu____15635,FStar_Syntax_Syntax.Tm_lazy uu____15636) ->
            let uu____15637 =
              let uu____15639 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15639  in
            check "lazy_r" uu____15637
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15684 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15684))
              &&
              (let uu____15688 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15688)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15692),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15694)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15754 =
               let uu____15756 = eq_quoteinfo qi1 qi2  in uu____15756 = Equal
                in
             check "tm_quoted qi" uu____15754) &&
              (let uu____15759 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15759)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15789 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15789) &&
                   (let uu____15793 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15793)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15812 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15812) &&
                    (let uu____15816 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15816))
                   &&
                   (let uu____15820 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15820)
             | uu____15823 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15829) -> fail "unk"
        | (uu____15831,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15833,uu____15834) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15836,uu____15837) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15839,uu____15840) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15842,uu____15843) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15845,uu____15846) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15848,uu____15849) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15869,uu____15870) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15886,uu____15887) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15895,uu____15896) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15914,uu____15915) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____15939,uu____15940) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____15955,uu____15956) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____15970,uu____15971) ->
            fail "bottom"
        | (uu____15979,FStar_Syntax_Syntax.Tm_bvar uu____15980) ->
            fail "bottom"
        | (uu____15982,FStar_Syntax_Syntax.Tm_name uu____15983) ->
            fail "bottom"
        | (uu____15985,FStar_Syntax_Syntax.Tm_fvar uu____15986) ->
            fail "bottom"
        | (uu____15988,FStar_Syntax_Syntax.Tm_constant uu____15989) ->
            fail "bottom"
        | (uu____15991,FStar_Syntax_Syntax.Tm_type uu____15992) ->
            fail "bottom"
        | (uu____15994,FStar_Syntax_Syntax.Tm_abs uu____15995) ->
            fail "bottom"
        | (uu____16015,FStar_Syntax_Syntax.Tm_arrow uu____16016) ->
            fail "bottom"
        | (uu____16032,FStar_Syntax_Syntax.Tm_refine uu____16033) ->
            fail "bottom"
        | (uu____16041,FStar_Syntax_Syntax.Tm_app uu____16042) ->
            fail "bottom"
        | (uu____16060,FStar_Syntax_Syntax.Tm_match uu____16061) ->
            fail "bottom"
        | (uu____16085,FStar_Syntax_Syntax.Tm_let uu____16086) ->
            fail "bottom"
        | (uu____16101,FStar_Syntax_Syntax.Tm_uvar uu____16102) ->
            fail "bottom"
        | (uu____16116,FStar_Syntax_Syntax.Tm_meta uu____16117) ->
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
               let uu____16152 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16152)
          (fun q1  ->
             fun q2  ->
               let uu____16164 =
                 let uu____16166 = eq_aqual q1 q2  in uu____16166 = Equal  in
               check "arg qual" uu____16164) a1 a2

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
               let uu____16191 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16191)
          (fun q1  ->
             fun q2  ->
               let uu____16203 =
                 let uu____16205 = eq_aqual q1 q2  in uu____16205 = Equal  in
               check "binder qual" uu____16203) b1 b2

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
        ((let uu____16219 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16219) &&
           (let uu____16223 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16223))
          && true

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
    fun uu____16228  ->
      fun uu____16229  ->
        match (uu____16228, uu____16229) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16356 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16356) &&
               (let uu____16360 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16360))
              &&
              (let uu____16364 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16406 -> false  in
               check "branch when" uu____16364)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16427 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16427) &&
           (let uu____16436 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16436))
          &&
          (let uu____16440 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16440)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16457 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16457 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16511 ->
        let uu____16526 =
          let uu____16528 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16528  in
        Prims.int_one + uu____16526
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16531 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16531
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16535 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16535
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16544 = sizeof t1  in (FStar_List.length us) + uu____16544
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16548) ->
        let uu____16573 = sizeof t1  in
        let uu____16575 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16590  ->
                 match uu____16590 with
                 | (bv,uu____16600) ->
                     let uu____16605 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16605) Prims.int_zero bs
           in
        uu____16573 + uu____16575
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____16634 = sizeof hd  in
        let uu____16636 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16651  ->
                 match uu____16651 with
                 | (arg,uu____16661) ->
                     let uu____16666 = sizeof arg  in acc + uu____16666)
            Prims.int_zero args
           in
        uu____16634 + uu____16636
    | uu____16669 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16683 =
        let uu____16684 = un_uinst t  in uu____16684.FStar_Syntax_Syntax.n
         in
      match uu____16683 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16689 -> false
  
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
           let uu____16750 = head_and_args t  in
           match uu____16750 with
           | (head,args) ->
               let uu____16805 =
                 let uu____16806 = FStar_Syntax_Subst.compress head  in
                 uu____16806.FStar_Syntax_Syntax.n  in
               (match uu____16805 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16832 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____16865 = is_fvar attr a  in Prims.op_Negation uu____16865)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      FStar_Errors.set_option_warning_callback_range
        (FStar_Pervasives_Native.Some r);
      (let set_options s =
         let uu____16887 = FStar_Options.set_options s  in
         match uu____16887 with
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
           ((let uu____16901 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____16901 (fun uu____16903  -> ()));
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
           let uu____16917 = FStar_Options.internal_pop ()  in
           if uu____16917
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
    | FStar_Syntax_Syntax.Tm_delayed uu____16949 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____16968 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____16983 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____16984 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____16985 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16994) ->
        let uu____17019 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17019 with
         | (bs1,t2) ->
             let uu____17028 =
               FStar_List.collect
                 (fun uu____17040  ->
                    match uu____17040 with
                    | (b,uu____17050) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17055 = unbound_variables t2  in
             FStar_List.append uu____17028 uu____17055)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17080 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17080 with
         | (bs1,c1) ->
             let uu____17089 =
               FStar_List.collect
                 (fun uu____17101  ->
                    match uu____17101 with
                    | (b,uu____17111) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17116 = unbound_variables_comp c1  in
             FStar_List.append uu____17089 uu____17116)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17125 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17125 with
         | (bs,t2) ->
             let uu____17148 =
               FStar_List.collect
                 (fun uu____17160  ->
                    match uu____17160 with
                    | (b1,uu____17170) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17175 = unbound_variables t2  in
             FStar_List.append uu____17148 uu____17175)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17204 =
          FStar_List.collect
            (fun uu____17218  ->
               match uu____17218 with
               | (x,uu____17230) -> unbound_variables x) args
           in
        let uu____17239 = unbound_variables t1  in
        FStar_List.append uu____17204 uu____17239
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17280 = unbound_variables t1  in
        let uu____17283 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17298 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17298 with
                  | (p,wopt,t2) ->
                      let uu____17320 = unbound_variables t2  in
                      let uu____17323 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17320 uu____17323))
           in
        FStar_List.append uu____17280 uu____17283
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17337) ->
        let uu____17378 = unbound_variables t1  in
        let uu____17381 =
          let uu____17384 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17415 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17384 uu____17415  in
        FStar_List.append uu____17378 uu____17381
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17456 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17459 =
          let uu____17462 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17465 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17470 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17472 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17472 with
                 | (uu____17493,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17462 uu____17465  in
        FStar_List.append uu____17456 uu____17459
    | FStar_Syntax_Syntax.Tm_let ((uu____17495,lbs),t1) ->
        let uu____17515 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17515 with
         | (lbs1,t2) ->
             let uu____17530 = unbound_variables t2  in
             let uu____17533 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17540 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17543 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17540 uu____17543) lbs1
                in
             FStar_List.append uu____17530 uu____17533)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17560 = unbound_variables t1  in
        let uu____17563 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17568,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17623  ->
                      match uu____17623 with
                      | (a,uu____17635) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17644,uu____17645,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17651,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17657 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17666 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17667 -> []  in
        FStar_List.append uu____17560 uu____17563

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17674) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17684) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17694 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17697 =
          FStar_List.collect
            (fun uu____17711  ->
               match uu____17711 with
               | (a,uu____17723) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17694 uu____17697

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
            let uu____17838 = head_and_args h  in
            (match uu____17838 with
             | (head,args) ->
                 let uu____17899 =
                   let uu____17900 = FStar_Syntax_Subst.compress head  in
                   uu____17900.FStar_Syntax_Syntax.n  in
                 (match uu____17899 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____17953 -> aux (h :: acc) t))
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
      let uu____17977 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____17977 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2513_18019 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2513_18019.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2513_18019.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2513_18019.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2513_18019.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2513_18019.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18027 =
      let uu____18028 = FStar_Syntax_Subst.compress t  in
      uu____18028.FStar_Syntax_Syntax.n  in
    match uu____18027 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18032,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18060)::uu____18061 ->
                  let pats' = unmeta pats  in
                  let uu____18121 = head_and_args pats'  in
                  (match uu____18121 with
                   | (head,uu____18140) ->
                       let uu____18165 =
                         let uu____18166 = un_uinst head  in
                         uu____18166.FStar_Syntax_Syntax.n  in
                       (match uu____18165 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18171 -> false))
              | uu____18173 -> false)
         | uu____18185 -> false)
    | uu____18187 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18203 =
      let uu____18220 = unmeta e  in head_and_args uu____18220  in
    match uu____18203 with
    | (head,args) ->
        let uu____18251 =
          let uu____18266 =
            let uu____18267 = un_uinst head  in
            uu____18267.FStar_Syntax_Syntax.n  in
          (uu____18266, args)  in
        (match uu____18251 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18285) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18309::(hd,uu____18311)::(tl,uu____18313)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18380 =
               let uu____18383 =
                 let uu____18386 = list_elements tl  in
                 FStar_Util.must uu____18386  in
               hd :: uu____18383  in
             FStar_Pervasives_Native.Some uu____18380
         | uu____18395 -> FStar_Pervasives_Native.None)
  
let (unthunk : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____18418 =
      let uu____18419 = FStar_Syntax_Subst.compress t  in
      uu____18419.FStar_Syntax_Syntax.n  in
    match uu____18418 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18424) ->
        let uu____18459 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18459 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18491 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18491
             then
               let uu____18496 =
                 let uu____18507 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18507]  in
               mk_app t uu____18496
             else e1)
    | uu____18534 ->
        let uu____18535 =
          let uu____18546 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18546]  in
        mk_app t uu____18535
  
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
        let uu____18607 = list_elements e  in
        match uu____18607 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18642 =
          let uu____18659 = unmeta p  in
          FStar_All.pipe_right uu____18659 head_and_args  in
        match uu____18642 with
        | (head,args) ->
            let uu____18710 =
              let uu____18725 =
                let uu____18726 = un_uinst head  in
                uu____18726.FStar_Syntax_Syntax.n  in
              (uu____18725, args)  in
            (match uu____18710 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18748,uu____18749)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18801 ->
                 let uu____18816 =
                   let uu____18822 =
                     let uu____18824 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18824
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____18822)  in
                 FStar_Errors.raise_error uu____18816
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____18867 =
            let uu____18884 = unmeta t1  in
            FStar_All.pipe_right uu____18884 head_and_args  in
          match uu____18867 with
          | (head,args) ->
              let uu____18931 =
                let uu____18946 =
                  let uu____18947 = un_uinst head  in
                  uu____18947.FStar_Syntax_Syntax.n  in
                (uu____18946, args)  in
              (match uu____18931 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____18966)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19003 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19033 = smt_pat_or t1  in
            (match uu____19033 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19055 = list_elements1 e  in
                 FStar_All.pipe_right uu____19055
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19085 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19085
                           (FStar_List.map one_pat)))
             | uu____19114 ->
                 let uu____19119 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19119])
        | uu____19174 ->
            let uu____19177 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19177]
         in
      let uu____19232 =
        let uu____19263 =
          let uu____19264 = FStar_Syntax_Subst.compress t  in
          uu____19264.FStar_Syntax_Syntax.n  in
        match uu____19263 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19319 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19319 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19386;
                        FStar_Syntax_Syntax.effect_name = uu____19387;
                        FStar_Syntax_Syntax.result_typ = uu____19388;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19390)::(post,uu____19392)::(pats,uu____19394)::[];
                        FStar_Syntax_Syntax.flags = uu____19395;_}
                      ->
                      let uu____19456 = lemma_pats pats  in
                      (binders1, pre, post, uu____19456)
                  | uu____19491 -> failwith "impos"))
        | uu____19523 -> failwith "Impos"  in
      match uu____19232 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19607 =
              let uu____19608 =
                let uu____19615 = mk_imp pre post1  in
                let uu____19618 =
                  let uu____19619 =
                    let uu____19640 =
                      FStar_Syntax_Syntax.binders_to_names binders  in
                    (uu____19640, patterns)  in
                  FStar_Syntax_Syntax.Meta_pattern uu____19619  in
                (uu____19615, uu____19618)  in
              FStar_Syntax_Syntax.Tm_meta uu____19608  in
            FStar_Syntax_Syntax.mk uu____19607 t.FStar_Syntax_Syntax.pos  in
          let quant =
            let uu____19664 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19664 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19694 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19705 -> true
    | uu____19707 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19718 -> true
    | uu____19720 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19738 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19739 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19740 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19741 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19742 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19743 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19744 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19745 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19748 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19751 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19738;
        FStar_Syntax_Syntax.bind_wp = uu____19739;
        FStar_Syntax_Syntax.stronger = uu____19740;
        FStar_Syntax_Syntax.if_then_else = uu____19741;
        FStar_Syntax_Syntax.ite_wp = uu____19742;
        FStar_Syntax_Syntax.close_wp = uu____19743;
        FStar_Syntax_Syntax.trivial = uu____19744;
        FStar_Syntax_Syntax.repr = uu____19745;
        FStar_Syntax_Syntax.return_repr = uu____19748;
        FStar_Syntax_Syntax.bind_repr = uu____19751
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____19783 =
        match uu____19783 with
        | (ts1,ts2) ->
            let uu____19794 = f ts1  in
            let uu____19795 = f ts2  in (uu____19794, uu____19795)
         in
      let uu____19796 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____19801 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____19806 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____19811 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____19816 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____19796;
        FStar_Syntax_Syntax.l_return = uu____19801;
        FStar_Syntax_Syntax.l_bind = uu____19806;
        FStar_Syntax_Syntax.l_subcomp = uu____19811;
        FStar_Syntax_Syntax.l_if_then_else = uu____19816
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
          let uu____19838 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____19838
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19840 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____19840
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19842 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____19842
  
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
    | uu____19857 -> FStar_Pervasives_Native.None
  
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
        let uu____19871 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19871
          (fun uu____19878  -> FStar_Pervasives_Native.Some uu____19878)
  
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
        let uu____19918 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19918
          (fun uu____19925  -> FStar_Pervasives_Native.Some uu____19925)
  
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
        let uu____19939 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19939
          (fun uu____19946  -> FStar_Pervasives_Native.Some uu____19946)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____19960  -> FStar_Pervasives_Native.Some uu____19960)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____19964  -> FStar_Pervasives_Native.Some uu____19964)
    | uu____19965 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19977 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19977
          (fun uu____19984  -> FStar_Pervasives_Native.Some uu____19984)
    | uu____19985 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____19999  -> FStar_Pervasives_Native.Some uu____19999)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20003  -> FStar_Pervasives_Native.Some uu____20003)
    | uu____20004 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20018  -> FStar_Pervasives_Native.Some uu____20018)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20022  -> FStar_Pervasives_Native.Some uu____20022)
    | uu____20023 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20047 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20048 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20050 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20050
          (fun uu____20057  -> FStar_Pervasives_Native.Some uu____20057)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun uu____20071  -> FStar_Pervasives_Native.Some uu____20071)
    | uu____20072 -> FStar_Pervasives_Native.None
  