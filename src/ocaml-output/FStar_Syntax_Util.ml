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
    | FStar_Syntax_Syntax.U_zero  -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1146 = univ_kernel u1  in
        (match uu____1146 with | (k,n) -> (k, (n + Prims.int_one)))
    | FStar_Syntax_Syntax.U_max uu____1163 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____1172 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____1187 = univ_kernel u  in FStar_Pervasives_Native.snd uu____1187
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____1207,uu____1208) ->
          failwith "Impossible: compare_univs"
      | (uu____1212,FStar_Syntax_Syntax.U_bvar uu____1213) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.int_zero
      | (FStar_Syntax_Syntax.U_unknown ,uu____1218) -> ~- Prims.int_one
      | (uu____1220,FStar_Syntax_Syntax.U_unknown ) -> Prims.int_one
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.int_zero
      | (FStar_Syntax_Syntax.U_zero ,uu____1223) -> ~- Prims.int_one
      | (uu____1225,FStar_Syntax_Syntax.U_zero ) -> Prims.int_one
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          let uu____1229 = FStar_Ident.text_of_id u11  in
          let uu____1231 = FStar_Ident.text_of_id u21  in
          FStar_String.compare uu____1229 uu____1231
      | (FStar_Syntax_Syntax.U_name uu____1233,FStar_Syntax_Syntax.U_unif
         uu____1234) -> ~- Prims.int_one
      | (FStar_Syntax_Syntax.U_unif uu____1244,FStar_Syntax_Syntax.U_name
         uu____1245) -> Prims.int_one
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____1273 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____1275 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____1273 - uu____1275
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____1293 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____1293
                 (fun uu____1309  ->
                    match uu____1309 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> Prims.int_zero
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> Prims.int_zero
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____1337,uu____1338) -> ~- Prims.int_one
      | (uu____1342,FStar_Syntax_Syntax.U_max uu____1343) -> Prims.int_one
      | uu____1347 ->
          let uu____1352 = univ_kernel u1  in
          (match uu____1352 with
           | (k1,n1) ->
               let uu____1363 = univ_kernel u2  in
               (match uu____1363 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = Prims.int_zero then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1394 = compare_univs u1 u2  in uu____1394 = Prims.int_zero
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1413 =
        let uu____1414 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1414;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1413
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1434 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1443 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1466 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1475 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1502 =
          let uu____1503 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1503  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1502;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1532 =
          let uu____1533 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1533  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1532;
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
      let uu___223_1569 = c  in
      let uu____1570 =
        let uu____1571 =
          let uu___225_1572 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___225_1572.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___225_1572.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___225_1572.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___225_1572.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1571  in
      {
        FStar_Syntax_Syntax.n = uu____1570;
        FStar_Syntax_Syntax.pos = (uu___223_1569.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___223_1569.FStar_Syntax_Syntax.vars)
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
    | uu____1612 ->
        failwith "Assertion failed: Computation type without universe"
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1634)::[] -> wp
      | uu____1659 ->
          let uu____1670 =
            let uu____1672 =
              FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name  in
            let uu____1674 =
              let uu____1676 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length
                 in
              FStar_All.pipe_right uu____1676 FStar_Util.string_of_int  in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args"
              uu____1672 uu____1674
             in
          failwith uu____1670
       in
    let uu____1700 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1700, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1714 -> true
    | FStar_Syntax_Syntax.GTotal uu____1724 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1749  ->
               match uu___0_1749 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1753 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1770  ->
            match uu___1_1770 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1774 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1806 -> true
    | FStar_Syntax_Syntax.GTotal uu____1816 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_1831  ->
                   match uu___2_1831 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1834 -> false)))
  
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
    let uu____1875 =
      let uu____1876 = FStar_Syntax_Subst.compress t  in
      uu____1876.FStar_Syntax_Syntax.n  in
    match uu____1875 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1880,c) -> is_pure_or_ghost_comp c
    | uu____1902 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1917 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1926 =
      let uu____1927 = FStar_Syntax_Subst.compress t  in
      uu____1927.FStar_Syntax_Syntax.n  in
    match uu____1926 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1931,c) -> is_lemma_comp c
    | uu____1953 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1961 =
      let uu____1962 = FStar_Syntax_Subst.compress t  in
      uu____1962.FStar_Syntax_Syntax.n  in
    match uu____1961 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____1966) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____1992) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2029,t1,uu____2031) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2057,uu____2058) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2100) -> head_of t1
    | uu____2105 -> t
  
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
    | uu____2183 -> (t1, [])
  
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
        let uu____2265 = head_and_args' head  in
        (match uu____2265 with
         | (head1,args') -> (head1, (FStar_List.append args' args)))
    | uu____2334 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2361) ->
        FStar_Syntax_Subst.compress t2
    | uu____2366 -> t1
  
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
                (fun uu___3_2384  ->
                   match uu___3_2384 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2387 -> false)))
    | uu____2389 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2406) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2416) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2445 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2454 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___364_2466 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___364_2466.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___364_2466.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___364_2466.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___364_2466.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2482  ->
            match uu___4_2482 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2486 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2494 -> []
    | FStar_Syntax_Syntax.GTotal uu____2511 -> []
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
    | uu____2555 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2565,uu____2566) ->
        unascribe e2
    | uu____2607 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2660,uu____2661) ->
          ascribe t' k
      | uu____2702 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2729 =
      let uu____2738 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2738  in
    uu____2729 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2794 =
      let uu____2795 = FStar_Syntax_Subst.compress t  in
      uu____2795.FStar_Syntax_Syntax.n  in
    match uu____2794 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2799 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2799
    | uu____2800 -> t
  
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2807 =
      let uu____2808 = FStar_Syntax_Subst.compress t  in
      uu____2808.FStar_Syntax_Syntax.n  in
    match uu____2807 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2812 ->
             let uu____2821 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____2821
         | uu____2822 -> t)
    | uu____2823 -> t
  
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
      | uu____2848 -> false
  
let unlazy_as_t :
  'uuuuuu2861 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'uuuuuu2861
  =
  fun k  ->
    fun t  ->
      let uu____2872 =
        let uu____2873 = FStar_Syntax_Subst.compress t  in
        uu____2873.FStar_Syntax_Syntax.n  in
      match uu____2872 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2878;
            FStar_Syntax_Syntax.rng = uu____2879;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____2882 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____2923 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2923;
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
    let uu____2936 =
      let uu____2951 = unascribe t  in head_and_args' uu____2951  in
    match uu____2936 with
    | (hd,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2985 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2996 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____3007 -> false
  
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
      | (NotEqual ,uu____3057) -> NotEqual
      | (uu____3058,NotEqual ) -> NotEqual
      | (Unknown ,uu____3059) -> Unknown
      | (uu____3060,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___5_3169 = if uu___5_3169 then Equal else Unknown  in
      let equal_iff uu___6_3180 = if uu___6_3180 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____3201 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3223 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3223
        then
          let uu____3227 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3304  ->
                    match uu____3304 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3345 = eq_tm a1 a2  in
                        eq_inj acc uu____3345) Equal) uu____3227
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3359 =
          let uu____3376 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3376 head_and_args  in
        match uu____3359 with
        | (head1,args1) ->
            let uu____3429 =
              let uu____3446 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3446 head_and_args  in
            (match uu____3429 with
             | (head2,args2) ->
                 let uu____3499 =
                   let uu____3504 =
                     let uu____3505 = un_uinst head1  in
                     uu____3505.FStar_Syntax_Syntax.n  in
                   let uu____3508 =
                     let uu____3509 = un_uinst head2  in
                     uu____3509.FStar_Syntax_Syntax.n  in
                   (uu____3504, uu____3508)  in
                 (match uu____3499 with
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
                  | uu____3536 -> FStar_Pervasives_Native.None))
         in
      let uu____3549 =
        let uu____3554 =
          let uu____3555 = unmeta t11  in uu____3555.FStar_Syntax_Syntax.n
           in
        let uu____3558 =
          let uu____3559 = unmeta t21  in uu____3559.FStar_Syntax_Syntax.n
           in
        (uu____3554, uu____3558)  in
      match uu____3549 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3565,uu____3566) ->
          let uu____3567 = unlazy t11  in eq_tm uu____3567 t21
      | (uu____3568,FStar_Syntax_Syntax.Tm_lazy uu____3569) ->
          let uu____3570 = unlazy t21  in eq_tm t11 uu____3570
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          let uu____3573 = FStar_Syntax_Syntax.bv_eq a b  in
          equal_if uu____3573
      | uu____3575 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3599 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3599
            (fun uu____3647  ->
               match uu____3647 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3662 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3662
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3676 = eq_tm f g  in
          eq_and uu____3676
            (fun uu____3679  ->
               let uu____3680 = eq_univs_list us vs  in equal_if uu____3680)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3682),uu____3683) -> Unknown
      | (uu____3684,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3685)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3688 = FStar_Const.eq_const c d  in equal_iff uu____3688
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3691)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3693))) ->
          let uu____3722 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3722
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3776 =
            let uu____3781 =
              let uu____3782 = un_uinst h1  in
              uu____3782.FStar_Syntax_Syntax.n  in
            let uu____3785 =
              let uu____3786 = un_uinst h2  in
              uu____3786.FStar_Syntax_Syntax.n  in
            (uu____3781, uu____3785)  in
          (match uu____3776 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3792 =
                    let uu____3794 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3794  in
                  FStar_List.mem uu____3792 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3796 ->
               let uu____3801 = eq_tm h1 h2  in
               eq_and uu____3801 (fun uu____3803  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3909 = FStar_List.zip bs1 bs2  in
            let uu____3972 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____4009  ->
                 fun a  ->
                   match uu____4009 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4102  -> branch_matches b1 b2))
              uu____3909 uu____3972
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v) ->
          let uu____4107 = eq_univs u v  in equal_if uu____4107
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____4121 = eq_quoteinfo q1 q2  in
          eq_and uu____4121 (fun uu____4123  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____4136 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4136 (fun uu____4138  -> eq_tm phi1 phi2)
      | uu____4139 -> Unknown

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
      | ([],uu____4211) -> NotEqual
      | (uu____4242,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          let uu____4331 =
            let uu____4333 = FStar_Syntax_Syntax.bv_eq x1 x2  in
            Prims.op_Negation uu____4333  in
          if uu____4331
          then NotEqual
          else
            (let uu____4338 = eq_tm t1 t2  in
             match uu____4338 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4339 = eq_antiquotes a11 a21  in
                 (match uu____4339 with
                  | NotEqual  -> NotEqual
                  | uu____4340 -> Unknown)
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
        | (uu____4424,uu____4425) -> false  in
      let uu____4435 = b1  in
      match uu____4435 with
      | (p1,w1,t1) ->
          let uu____4469 = b2  in
          (match uu____4469 with
           | (p2,w2,t2) ->
               let uu____4503 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4503
               then
                 let uu____4506 =
                   (let uu____4510 = eq_tm t1 t2  in uu____4510 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4519 = eq_tm t11 t21  in
                             uu____4519 = Equal) w1 w2)
                    in
                 (if uu____4506 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4584)::a11,(b,uu____4587)::b1) ->
          let uu____4661 = eq_tm a b  in
          (match uu____4661 with
           | Equal  -> eq_args a11 b1
           | uu____4662 -> Unknown)
      | uu____4663 -> Unknown

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
      | (FStar_Pervasives_Native.None ,uu____4718) -> NotEqual
      | (uu____4725,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4755 -> NotEqual
  
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4772) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4778,uu____4779) ->
        unrefine t2
    | uu____4820 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4828 =
      let uu____4829 = FStar_Syntax_Subst.compress t  in
      uu____4829.FStar_Syntax_Syntax.n  in
    match uu____4828 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4833 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4848) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4853 ->
        let uu____4870 =
          let uu____4871 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____4871 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____4870 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4934,uu____4935) ->
        is_uvar t1
    | uu____4976 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4985 =
      let uu____4986 = unrefine t  in uu____4986.FStar_Syntax_Syntax.n  in
    match uu____4985 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head,uu____4992) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5018) -> is_unit t1
    | uu____5023 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5032 =
      let uu____5033 = FStar_Syntax_Subst.compress t  in
      uu____5033.FStar_Syntax_Syntax.n  in
    match uu____5032 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5038 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5047 =
      let uu____5048 = FStar_Syntax_Subst.compress e  in
      uu____5048.FStar_Syntax_Syntax.n  in
    match uu____5047 with
    | FStar_Syntax_Syntax.Tm_abs uu____5052 -> true
    | uu____5072 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5081 =
      let uu____5082 = FStar_Syntax_Subst.compress t  in
      uu____5082.FStar_Syntax_Syntax.n  in
    match uu____5081 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5086 -> true
    | uu____5102 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5112) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5118,uu____5119) ->
        pre_typ t2
    | uu____5160 -> t1
  
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
      let uu____5185 =
        let uu____5186 = un_uinst typ1  in uu____5186.FStar_Syntax_Syntax.n
         in
      match uu____5185 with
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let head1 = un_uinst head  in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5251 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5281 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5302,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5309) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5314,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5325,uu____5326,uu____5327,uu____5328,uu____5329) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5339,uu____5340,uu____5341,uu____5342) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5348,uu____5349,uu____5350,uu____5351,uu____5352) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5360,uu____5361) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5363,uu____5364) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5366 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5367 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5368 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5369 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5382 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5406 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5432  ->
    match uu___7_5432 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'uuuuuu5446 'uuuuuu5447 .
    ('uuuuuu5446 FStar_Syntax_Syntax.syntax * 'uuuuuu5447) ->
      FStar_Range.range
  =
  fun uu____5458  ->
    match uu____5458 with | (hd,uu____5466) -> hd.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'uuuuuu5480 'uuuuuu5481 .
    ('uuuuuu5480 FStar_Syntax_Syntax.syntax * 'uuuuuu5481) Prims.list ->
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
      | uu____5579 ->
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
      let uu____5638 =
        FStar_List.map
          (fun uu____5665  ->
             match uu____5665 with
             | (bv,aq) ->
                 let uu____5684 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5684, aq)) bs
         in
      mk_app f uu____5638
  
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
          (let uu____5735 =
             let uu____5741 =
               let uu____5743 =
                 let uu____5745 = FStar_Ident.ident_of_lid lid  in
                 FStar_Ident.text_of_id uu____5745  in
               mk_field_projector_name_from_string uu____5743 itext  in
             let uu____5746 = FStar_Ident.range_of_id i  in
             (uu____5741, uu____5746)  in
           FStar_Ident.mk_ident uu____5735)
         in
      let uu____5748 =
        let uu____5749 = FStar_Ident.ns_of_lid lid  in
        FStar_List.append uu____5749 [newi]  in
      FStar_Ident.lid_of_ids uu____5748
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5771 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5771
          then
            let uu____5774 =
              let uu____5780 =
                let uu____5782 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5782  in
              let uu____5785 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5780, uu____5785)  in
            FStar_Ident.mk_ident uu____5774
          else x.FStar_Syntax_Syntax.ppname  in
        mk_field_projector_name_from_ident lid nm
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5800) -> ses
    | uu____5809 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____5824 = FStar_Syntax_Unionfind.find uv  in
      match uu____5824 with
      | FStar_Pervasives_Native.Some uu____5827 ->
          let uu____5828 =
            let uu____5830 =
              let uu____5832 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5832  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5830  in
          failwith uu____5828
      | uu____5837 -> FStar_Syntax_Unionfind.change uv t
  
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
            (let uu____5861 = FStar_Ident.text_of_id l1b  in
             let uu____5863 = FStar_Ident.text_of_id l2b  in
             uu____5861 = uu____5863)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5892 = FStar_Ident.text_of_id x1  in
                      let uu____5894 = FStar_Ident.text_of_id x2  in
                      uu____5892 = uu____5894) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5903 = FStar_Ident.text_of_id x1  in
                    let uu____5905 = FStar_Ident.text_of_id x2  in
                    uu____5903 = uu____5905) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____5934 = FStar_Ident.text_of_id x1  in
                      let uu____5936 = FStar_Ident.text_of_id x2  in
                      uu____5934 = uu____5936) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____5945 = FStar_Ident.text_of_id x1  in
                    let uu____5947 = FStar_Ident.text_of_id x2  in
                    uu____5945 = uu____5947) f1 f2)
      | uu____5950 -> q1 = q2
  
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
              let uu____5996 =
                let uu___992_5997 = rc  in
                let uu____5998 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___992_5997.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____5998;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___992_5997.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____5996
           in
        match bs with
        | [] -> t
        | uu____6015 ->
            let body =
              let uu____6017 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6017  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6047 =
                   let uu____6054 =
                     let uu____6055 =
                       let uu____6074 =
                         let uu____6083 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6083 bs'  in
                       let uu____6098 = close_lopt lopt'  in
                       (uu____6074, t1, uu____6098)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6055  in
                   FStar_Syntax_Syntax.mk uu____6054  in
                 uu____6047 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6113 ->
                 let uu____6114 =
                   let uu____6121 =
                     let uu____6122 =
                       let uu____6141 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6150 = close_lopt lopt  in
                       (uu____6141, body, uu____6150)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6122  in
                   FStar_Syntax_Syntax.mk uu____6121  in
                 uu____6114 FStar_Pervasives_Native.None
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
      | uu____6206 ->
          let uu____6215 =
            let uu____6222 =
              let uu____6223 =
                let uu____6238 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6247 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6238, uu____6247)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6223  in
            FStar_Syntax_Syntax.mk uu____6222  in
          uu____6215 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6296 =
        let uu____6297 = FStar_Syntax_Subst.compress t  in
        uu____6297.FStar_Syntax_Syntax.n  in
      match uu____6296 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6327) ->
               let uu____6336 =
                 let uu____6337 = FStar_Syntax_Subst.compress tres  in
                 uu____6337.FStar_Syntax_Syntax.n  in
               (match uu____6336 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6380 -> t)
           | uu____6381 -> t)
      | uu____6382 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6400 =
        let uu____6401 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6401 t.FStar_Syntax_Syntax.pos  in
      let uu____6402 =
        let uu____6409 =
          let uu____6410 =
            let uu____6417 =
              let uu____6420 =
                let uu____6421 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6421]  in
              FStar_Syntax_Subst.close uu____6420 t  in
            (b, uu____6417)  in
          FStar_Syntax_Syntax.Tm_refine uu____6410  in
        FStar_Syntax_Syntax.mk uu____6409  in
      uu____6402 FStar_Pervasives_Native.None uu____6400
  
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
        let uu____6501 = is_total_comp c  in
        if uu____6501
        then
          let uu____6516 = arrow_formals_comp_ln (comp_result c)  in
          (match uu____6516 with
           | (bs',k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6583;
           FStar_Syntax_Syntax.index = uu____6584;
           FStar_Syntax_Syntax.sort = s;_},uu____6586)
        ->
        let rec aux s1 k2 =
          let uu____6617 =
            let uu____6618 = FStar_Syntax_Subst.compress s1  in
            uu____6618.FStar_Syntax_Syntax.n  in
          match uu____6617 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6633 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6648;
                 FStar_Syntax_Syntax.index = uu____6649;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6651)
              -> aux s2 k2
          | uu____6659 ->
              let uu____6660 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6660)
           in
        aux s k1
    | uu____6675 ->
        let uu____6676 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6676)
  
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let uu____6701 = arrow_formals_comp_ln k  in
    match uu____6701 with | (bs,c) -> FStar_Syntax_Subst.open_comp bs c
  
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6756 = arrow_formals_comp_ln k  in
    match uu____6756 with | (bs,c) -> (bs, (comp_result c))
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6823 = arrow_formals_comp k  in
    match uu____6823 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6925 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6925 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____6949 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_6958  ->
                         match uu___8_6958 with
                         | FStar_Syntax_Syntax.DECREASES uu____6960 -> true
                         | uu____6964 -> false))
                  in
               (match uu____6949 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____6999 ->
                    let uu____7002 = is_total_comp c1  in
                    if uu____7002
                    then
                      let uu____7021 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7021 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7114;
             FStar_Syntax_Syntax.index = uu____7115;
             FStar_Syntax_Syntax.sort = k2;_},uu____7117)
          -> arrow_until_decreases k2
      | uu____7125 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7146 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7146 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7200 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7221 =
                 FStar_Common.tabulate n_univs (fun uu____7227  -> false)  in
               let uu____7230 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7255  ->
                         match uu____7255 with
                         | (x,uu____7264) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7221 uu____7230)
           in
        ((n_univs + (FStar_List.length bs)), uu____7200)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7320 =
            let uu___1119_7321 = rc  in
            let uu____7322 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1119_7321.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7322;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1119_7321.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7320
      | uu____7331 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7365 =
        let uu____7366 =
          let uu____7369 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7369  in
        uu____7366.FStar_Syntax_Syntax.n  in
      match uu____7365 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7415 = aux t2 what  in
          (match uu____7415 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7487 -> ([], t1, abs_body_lcomp)  in
    let uu____7504 = aux t FStar_Pervasives_Native.None  in
    match uu____7504 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7552 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7552 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let no_acc uu____7586 =
      match uu____7586 with
      | (b,aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true )) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7600 -> aq  in
          (b, aq1)
       in
    let uu____7605 = arrow_formals_comp_ln t  in
    match uu____7605 with
    | (bs,c) ->
        (match bs with
         | [] -> t
         | uu____7642 ->
             let uu____7651 =
               let uu____7658 =
                 let uu____7659 =
                   let uu____7674 = FStar_List.map no_acc bs  in
                   (uu____7674, c)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____7659  in
               FStar_Syntax_Syntax.mk uu____7658  in
             uu____7651 FStar_Pervasives_Native.None
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
                    | (FStar_Pervasives_Native.None ,uu____7845) -> def
                    | (uu____7856,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____7868) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu____7884  ->
                                  FStar_Syntax_Syntax.U_name uu____7884))
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
            let uu____7966 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____7966 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____8001 ->
            let t' = arrow binders c  in
            let uu____8013 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____8013 with
             | (uvs1,t'1) ->
                 let uu____8034 =
                   let uu____8035 = FStar_Syntax_Subst.compress t'1  in
                   uu____8035.FStar_Syntax_Syntax.n  in
                 (match uu____8034 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8084 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8109 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Parser_Const.is_tuple_constructor_string uu____8109
    | uu____8111 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8122 -> false
  
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
      let uu____8185 =
        let uu____8186 = pre_typ t  in uu____8186.FStar_Syntax_Syntax.n  in
      match uu____8185 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8191 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8205 =
        let uu____8206 = pre_typ t  in uu____8206.FStar_Syntax_Syntax.n  in
      match uu____8205 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8210 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8212) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8238) ->
          is_constructed_typ t1 lid
      | uu____8243 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8256 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8257 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8258 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8260) -> get_tycon t2
    | uu____8285 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8293 =
      let uu____8294 = un_uinst t  in uu____8294.FStar_Syntax_Syntax.n  in
    match uu____8293 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8299 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8313 =
        let uu____8317 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8317  in
      match uu____8313 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8349 -> false
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
  fun uu____8368  ->
    let u =
      let uu____8374 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left
        (fun uu____8391  -> FStar_Syntax_Syntax.U_unif uu____8391) uu____8374
       in
    let uu____8392 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8392, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8405 = eq_tm a a'  in
      match uu____8405 with | Equal  -> true | uu____8408 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8413 =
    let uu____8420 =
      let uu____8421 =
        let uu____8422 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8422
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8421  in
    FStar_Syntax_Syntax.mk uu____8420  in
  uu____8413 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8535 =
            let uu____8538 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8539 =
              let uu____8546 =
                let uu____8547 =
                  let uu____8564 =
                    let uu____8575 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8584 =
                      let uu____8595 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8595]  in
                    uu____8575 :: uu____8584  in
                  (tand, uu____8564)  in
                FStar_Syntax_Syntax.Tm_app uu____8547  in
              FStar_Syntax_Syntax.mk uu____8546  in
            uu____8539 FStar_Pervasives_Native.None uu____8538  in
          FStar_Pervasives_Native.Some uu____8535
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8672 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8673 =
          let uu____8680 =
            let uu____8681 =
              let uu____8698 =
                let uu____8709 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8718 =
                  let uu____8729 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8729]  in
                uu____8709 :: uu____8718  in
              (op_t, uu____8698)  in
            FStar_Syntax_Syntax.Tm_app uu____8681  in
          FStar_Syntax_Syntax.mk uu____8680  in
        uu____8673 FStar_Pervasives_Native.None uu____8672
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8786 =
      let uu____8793 =
        let uu____8794 =
          let uu____8811 =
            let uu____8822 = FStar_Syntax_Syntax.as_arg phi  in [uu____8822]
             in
          (t_not, uu____8811)  in
        FStar_Syntax_Syntax.Tm_app uu____8794  in
      FStar_Syntax_Syntax.mk uu____8793  in
    uu____8786 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____9019 =
      let uu____9026 =
        let uu____9027 =
          let uu____9044 =
            let uu____9055 = FStar_Syntax_Syntax.as_arg e  in [uu____9055]
             in
          (b2t_v, uu____9044)  in
        FStar_Syntax_Syntax.Tm_app uu____9027  in
      FStar_Syntax_Syntax.mk uu____9026  in
    uu____9019 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9102 = head_and_args e  in
    match uu____9102 with
    | (hd,args) ->
        let uu____9147 =
          let uu____9162 =
            let uu____9163 = FStar_Syntax_Subst.compress hd  in
            uu____9163.FStar_Syntax_Syntax.n  in
          (uu____9162, args)  in
        (match uu____9147 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9180)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9215 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9237 =
      let uu____9238 = unmeta t  in uu____9238.FStar_Syntax_Syntax.n  in
    match uu____9237 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9243 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9266 = is_t_true t1  in
      if uu____9266
      then t2
      else
        (let uu____9273 = is_t_true t2  in
         if uu____9273 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9301 = is_t_true t1  in
      if uu____9301
      then t_true
      else
        (let uu____9308 = is_t_true t2  in
         if uu____9308 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9337 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9338 =
        let uu____9345 =
          let uu____9346 =
            let uu____9363 =
              let uu____9374 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9383 =
                let uu____9394 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9394]  in
              uu____9374 :: uu____9383  in
            (teq, uu____9363)  in
          FStar_Syntax_Syntax.Tm_app uu____9346  in
        FStar_Syntax_Syntax.mk uu____9345  in
      uu____9338 FStar_Pervasives_Native.None uu____9337
  
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
          let uu____9461 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9462 =
            let uu____9469 =
              let uu____9470 =
                let uu____9487 =
                  let uu____9498 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9507 =
                    let uu____9518 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9527 =
                      let uu____9538 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9538]  in
                    uu____9518 :: uu____9527  in
                  uu____9498 :: uu____9507  in
                (eq_inst, uu____9487)  in
              FStar_Syntax_Syntax.Tm_app uu____9470  in
            FStar_Syntax_Syntax.mk uu____9469  in
          uu____9462 FStar_Pervasives_Native.None uu____9461
  
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
        let uu____9615 =
          let uu____9622 =
            let uu____9623 =
              let uu____9640 =
                let uu____9651 = FStar_Syntax_Syntax.iarg t  in
                let uu____9660 =
                  let uu____9671 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9680 =
                    let uu____9691 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9691]  in
                  uu____9671 :: uu____9680  in
                uu____9651 :: uu____9660  in
              (t_has_type1, uu____9640)  in
            FStar_Syntax_Syntax.Tm_app uu____9623  in
          FStar_Syntax_Syntax.mk uu____9622  in
        uu____9615 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9768 =
          let uu____9775 =
            let uu____9776 =
              let uu____9793 =
                let uu____9804 = FStar_Syntax_Syntax.iarg t  in
                let uu____9813 =
                  let uu____9824 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____9824]  in
                uu____9804 :: uu____9813  in
              (t_with_type1, uu____9793)  in
            FStar_Syntax_Syntax.Tm_app uu____9776  in
          FStar_Syntax_Syntax.mk uu____9775  in
        uu____9768 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9871 =
    let uu____9878 =
      let uu____9879 =
        let uu____9886 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____9886, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____9879  in
    FStar_Syntax_Syntax.mk uu____9878  in
  uu____9871 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
        let uu____9969 =
          let uu____9976 =
            let uu____9977 =
              let uu____9994 =
                let uu____10005 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____10014 =
                  let uu____10025 =
                    let uu____10034 =
                      let uu____10035 =
                        let uu____10036 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10036]  in
                      abs uu____10035 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10034  in
                  [uu____10025]  in
                uu____10005 :: uu____10014  in
              (fa, uu____9994)  in
            FStar_Syntax_Syntax.Tm_app uu____9977  in
          FStar_Syntax_Syntax.mk uu____9976  in
        uu____9969 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10163 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10163
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10182 -> true
    | uu____10184 -> false
  
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
          let uu____10231 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10231, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10260 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10260, FStar_Pervasives_Native.None, t2)  in
        let uu____10274 =
          let uu____10275 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10275  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10274
  
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
      let uu____10351 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10354 =
        let uu____10365 = FStar_Syntax_Syntax.as_arg p  in [uu____10365]  in
      mk_app uu____10351 uu____10354
  
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
      let uu____10405 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10408 =
        let uu____10419 = FStar_Syntax_Syntax.as_arg p  in [uu____10419]  in
      mk_app uu____10405 uu____10408
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10454 = head_and_args t  in
    match uu____10454 with
    | (head,args) ->
        let head1 = unascribe head  in
        let head2 = un_uinst head1  in
        let uu____10503 =
          let uu____10518 =
            let uu____10519 = FStar_Syntax_Subst.compress head2  in
            uu____10519.FStar_Syntax_Syntax.n  in
          (uu____10518, args)  in
        (match uu____10503 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10538)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10604 =
                    let uu____10609 =
                      let uu____10610 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10610]  in
                    FStar_Syntax_Subst.open_term uu____10609 p  in
                  (match uu____10604 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10667 -> failwith "impossible"  in
                       let uu____10675 =
                         let uu____10677 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10677
                          in
                       if uu____10675
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10693 -> FStar_Pervasives_Native.None)
         | uu____10696 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10727 = head_and_args t  in
    match uu____10727 with
    | (head,args) ->
        let uu____10778 =
          let uu____10793 =
            let uu____10794 = FStar_Syntax_Subst.compress head  in
            uu____10794.FStar_Syntax_Syntax.n  in
          (uu____10793, args)  in
        (match uu____10778 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10816;
               FStar_Syntax_Syntax.vars = uu____10817;_},u::[]),(t1,uu____10820)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10867 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10902 = head_and_args t  in
    match uu____10902 with
    | (head,args) ->
        let uu____10953 =
          let uu____10968 =
            let uu____10969 = FStar_Syntax_Subst.compress head  in
            uu____10969.FStar_Syntax_Syntax.n  in
          (uu____10968, args)  in
        (match uu____10953 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10991;
               FStar_Syntax_Syntax.vars = uu____10992;_},u::[]),(t1,uu____10995)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11042 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11070 =
      let uu____11087 = unmeta t  in head_and_args uu____11087  in
    match uu____11070 with
    | (head,uu____11090) ->
        let uu____11115 =
          let uu____11116 = un_uinst head  in
          uu____11116.FStar_Syntax_Syntax.n  in
        (match uu____11115 with
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
         | uu____11121 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11141 =
      let uu____11142 = FStar_Syntax_Subst.compress t  in
      uu____11142.FStar_Syntax_Syntax.n  in
    match uu____11141 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11248 =
          let uu____11253 =
            let uu____11254 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11254  in
          (b, uu____11253)  in
        FStar_Pervasives_Native.Some uu____11248
    | uu____11259 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11282 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11282
      (fun uu____11310  ->
         match uu____11310 with
         | (b,c) ->
             let uu____11329 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11329 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11392 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11429 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11429
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11481 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11524 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11565 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____11951) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____11963) ->
          unmeta_monadic t
      | uu____11976 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12045 =
        match uu____12045 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12083  ->
                   match uu____12083 with
                   | (lid,out_lid) ->
                       let uu____12092 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12092
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12119 = head_and_args t  in
      match uu____12119 with
      | (hd,args) ->
          let uu____12164 =
            let uu____12165 = un_uinst hd  in
            uu____12165.FStar_Syntax_Syntax.n  in
          (match uu____12164 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12171 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12180 = un_squash t  in
      FStar_Util.bind_opt uu____12180
        (fun t1  ->
           let uu____12196 = head_and_args' t1  in
           match uu____12196 with
           | (hd,args) ->
               let uu____12235 =
                 let uu____12236 = un_uinst hd  in
                 uu____12236.FStar_Syntax_Syntax.n  in
               (match uu____12235 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12242 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12283,pats)) ->
          let uu____12321 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12321)
      | uu____12334 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12401 = head_and_args t1  in
        match uu____12401 with
        | (t2,args) ->
            let uu____12456 = un_uinst t2  in
            let uu____12457 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12498  ->
                      match uu____12498 with
                      | (t3,imp) ->
                          let uu____12517 = unascribe t3  in
                          (uu____12517, imp)))
               in
            (uu____12456, uu____12457)
         in
      let rec aux qopt out t1 =
        let uu____12568 = let uu____12592 = flat t1  in (qopt, uu____12592)
           in
        match uu____12568 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12632;
                 FStar_Syntax_Syntax.vars = uu____12633;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12636);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12637;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12638;_},uu____12639)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12741;
                 FStar_Syntax_Syntax.vars = uu____12742;_},uu____12743::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12746);
                  FStar_Syntax_Syntax.pos = uu____12747;
                  FStar_Syntax_Syntax.vars = uu____12748;_},uu____12749)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12866;
               FStar_Syntax_Syntax.vars = uu____12867;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____12870);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____12871;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____12872;_},uu____12873)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12966 =
              let uu____12970 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____12970  in
            aux uu____12966 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____12980;
               FStar_Syntax_Syntax.vars = uu____12981;_},uu____12982::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____12985);
                FStar_Syntax_Syntax.pos = uu____12986;
                FStar_Syntax_Syntax.vars = uu____12987;_},uu____12988)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13097 =
              let uu____13101 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13101  in
            aux uu____13097 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13111) ->
            let bs = FStar_List.rev out  in
            let uu____13164 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13164 with
             | (bs1,t2) ->
                 let uu____13173 = patterns t2  in
                 (match uu____13173 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13223 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13278 = un_squash t  in
      FStar_Util.bind_opt uu____13278
        (fun t1  ->
           let uu____13293 = arrow_one t1  in
           match uu____13293 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13308 =
                 let uu____13310 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13310  in
               if uu____13308
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13320 = comp_to_comp_typ_nouniv c  in
                    uu____13320.FStar_Syntax_Syntax.result_typ  in
                  let uu____13321 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13321
                  then
                    let uu____13328 = patterns q  in
                    match uu____13328 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13391 =
                       let uu____13392 =
                         let uu____13397 =
                           let uu____13398 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13409 =
                             let uu____13420 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13420]  in
                           uu____13398 :: uu____13409  in
                         (FStar_Parser_Const.imp_lid, uu____13397)  in
                       BaseConn uu____13392  in
                     FStar_Pervasives_Native.Some uu____13391))
           | uu____13453 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13461 = un_squash t  in
      FStar_Util.bind_opt uu____13461
        (fun t1  ->
           let uu____13492 = head_and_args' t1  in
           match uu____13492 with
           | (hd,args) ->
               let uu____13531 =
                 let uu____13546 =
                   let uu____13547 = un_uinst hd  in
                   uu____13547.FStar_Syntax_Syntax.n  in
                 (uu____13546, args)  in
               (match uu____13531 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13564)::(a2,uu____13566)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13617 =
                      let uu____13618 = FStar_Syntax_Subst.compress a2  in
                      uu____13618.FStar_Syntax_Syntax.n  in
                    (match uu____13617 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13625) ->
                         let uu____13660 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13660 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13713 -> failwith "impossible"  in
                              let uu____13721 = patterns q1  in
                              (match uu____13721 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13782 -> FStar_Pervasives_Native.None)
                | uu____13783 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13806 = destruct_sq_forall phi  in
          (match uu____13806 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13816  ->
                    FStar_Pervasives_Native.Some uu____13816)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13823 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____13829 = destruct_sq_exists phi  in
          (match uu____13829 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13839  ->
                    FStar_Pervasives_Native.Some uu____13839)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13846 -> f1)
      | uu____13849 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____13853 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____13853
      (fun uu____13858  ->
         let uu____13859 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____13859
           (fun uu____13864  ->
              let uu____13865 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____13865
                (fun uu____13870  ->
                   let uu____13871 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____13871
                     (fun uu____13876  ->
                        let uu____13877 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____13877
                          (fun uu____13881  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____13899 =
            let uu____13904 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____13904  in
          let uu____13905 =
            let uu____13906 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____13906  in
          let uu____13909 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13899 a.FStar_Syntax_Syntax.action_univs uu____13905
            FStar_Parser_Const.effect_Tot_lid uu____13909 [] pos
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
    let uu____13935 =
      let uu____13942 =
        let uu____13943 =
          let uu____13960 =
            let uu____13971 = FStar_Syntax_Syntax.as_arg t  in [uu____13971]
             in
          (reify_, uu____13960)  in
        FStar_Syntax_Syntax.Tm_app uu____13943  in
      FStar_Syntax_Syntax.mk uu____13942  in
    uu____13935 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14023 =
        let uu____14030 =
          let uu____14031 =
            let uu____14032 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14032  in
          FStar_Syntax_Syntax.Tm_constant uu____14031  in
        FStar_Syntax_Syntax.mk uu____14030  in
      uu____14023 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14034 =
      let uu____14041 =
        let uu____14042 =
          let uu____14059 =
            let uu____14070 = FStar_Syntax_Syntax.as_arg t  in [uu____14070]
             in
          (reflect_, uu____14059)  in
        FStar_Syntax_Syntax.Tm_app uu____14042  in
      FStar_Syntax_Syntax.mk uu____14041  in
    uu____14034 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
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
            let uu____14469 =
              let uu____14470 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14470  in
            FStar_Syntax_Syntax.mk uu____14469  in
          uu____14462 FStar_Pervasives_Native.None rng  in
        let cons args pos =
          let uu____14484 =
            let uu____14489 =
              let uu____14490 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14490
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14489 args  in
          uu____14484 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14504 =
            let uu____14509 =
              let uu____14510 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14510
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14509 args  in
          uu____14504 FStar_Pervasives_Native.None pos  in
        let uu____14511 =
          let uu____14512 =
            let uu____14513 = FStar_Syntax_Syntax.iarg typ  in [uu____14513]
             in
          nil uu____14512 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14547 =
                 let uu____14548 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14557 =
                   let uu____14568 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14577 =
                     let uu____14588 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14588]  in
                   uu____14568 :: uu____14577  in
                 uu____14548 :: uu____14557  in
               cons uu____14547 t.FStar_Syntax_Syntax.pos) l uu____14511
  
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
        | uu____14697 -> false
  
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
          | uu____14811 -> false
  
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
        | uu____14977 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15015 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15015
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
        let t11 = let uu____15219 = unmeta_safe t1  in canon_app uu____15219
           in
        let t21 = let uu____15225 = unmeta_safe t2  in canon_app uu____15225
           in
        let uu____15228 =
          let uu____15233 =
            let uu____15234 =
              let uu____15237 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15237  in
            uu____15234.FStar_Syntax_Syntax.n  in
          let uu____15238 =
            let uu____15239 =
              let uu____15242 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15242  in
            uu____15239.FStar_Syntax_Syntax.n  in
          (uu____15233, uu____15238)  in
        match uu____15228 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15244,uu____15245) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15254,FStar_Syntax_Syntax.Tm_uinst uu____15255) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15264,uu____15265) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15282,FStar_Syntax_Syntax.Tm_delayed uu____15283) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15300,uu____15301) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15330,FStar_Syntax_Syntax.Tm_ascribed uu____15331) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15370 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15370
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15375 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15375
        | (FStar_Syntax_Syntax.Tm_type
           uu____15378,FStar_Syntax_Syntax.Tm_type uu____15379) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15437 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15437) &&
              (let uu____15447 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15447)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15496 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15496) &&
              (let uu____15506 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15506)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15523 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15523) &&
              (let uu____15527 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15527)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15584 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15584) &&
              (let uu____15588 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15588)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15677 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15677) &&
              (let uu____15681 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15681)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15698,uu____15699) ->
            let uu____15700 =
              let uu____15702 = unlazy t11  in
              term_eq_dbg dbg uu____15702 t21  in
            check "lazy_l" uu____15700
        | (uu____15704,FStar_Syntax_Syntax.Tm_lazy uu____15705) ->
            let uu____15706 =
              let uu____15708 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15708  in
            check "lazy_r" uu____15706
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15753 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15753))
              &&
              (let uu____15757 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15757)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15761),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15763)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____15821 =
               let uu____15823 = eq_quoteinfo qi1 qi2  in uu____15823 = Equal
                in
             check "tm_quoted qi" uu____15821) &&
              (let uu____15826 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____15826)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____15856 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____15856) &&
                   (let uu____15860 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____15860)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____15879 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____15879) &&
                    (let uu____15883 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____15883))
                   &&
                   (let uu____15887 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____15887)
             | uu____15890 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____15896) -> fail "unk"
        | (uu____15898,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15900,uu____15901) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15903,uu____15904) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15906,uu____15907) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15909,uu____15910) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15912,uu____15913) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15915,uu____15916) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15936,uu____15937) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15953,uu____15954) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15962,uu____15963) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15981,uu____15982) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16006,uu____16007) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16022,uu____16023) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16037,uu____16038) ->
            fail "bottom"
        | (uu____16046,FStar_Syntax_Syntax.Tm_bvar uu____16047) ->
            fail "bottom"
        | (uu____16049,FStar_Syntax_Syntax.Tm_name uu____16050) ->
            fail "bottom"
        | (uu____16052,FStar_Syntax_Syntax.Tm_fvar uu____16053) ->
            fail "bottom"
        | (uu____16055,FStar_Syntax_Syntax.Tm_constant uu____16056) ->
            fail "bottom"
        | (uu____16058,FStar_Syntax_Syntax.Tm_type uu____16059) ->
            fail "bottom"
        | (uu____16061,FStar_Syntax_Syntax.Tm_abs uu____16062) ->
            fail "bottom"
        | (uu____16082,FStar_Syntax_Syntax.Tm_arrow uu____16083) ->
            fail "bottom"
        | (uu____16099,FStar_Syntax_Syntax.Tm_refine uu____16100) ->
            fail "bottom"
        | (uu____16108,FStar_Syntax_Syntax.Tm_app uu____16109) ->
            fail "bottom"
        | (uu____16127,FStar_Syntax_Syntax.Tm_match uu____16128) ->
            fail "bottom"
        | (uu____16152,FStar_Syntax_Syntax.Tm_let uu____16153) ->
            fail "bottom"
        | (uu____16168,FStar_Syntax_Syntax.Tm_uvar uu____16169) ->
            fail "bottom"
        | (uu____16183,FStar_Syntax_Syntax.Tm_meta uu____16184) ->
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
               let uu____16219 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16219)
          (fun q1  ->
             fun q2  ->
               let uu____16231 =
                 let uu____16233 = eq_aqual q1 q2  in uu____16233 = Equal  in
               check "arg qual" uu____16231) a1 a2

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
               let uu____16258 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16258)
          (fun q1  ->
             fun q2  ->
               let uu____16270 =
                 let uu____16272 = eq_aqual q1 q2  in uu____16272 = Equal  in
               check "binder qual" uu____16270) b1 b2

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
        ((let uu____16286 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16286) &&
           (let uu____16290 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16290))
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
    fun uu____16300  ->
      fun uu____16301  ->
        match (uu____16300, uu____16301) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16428 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16428) &&
               (let uu____16432 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16432))
              &&
              (let uu____16436 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16478 -> false  in
               check "branch when" uu____16436)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16499 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16499) &&
           (let uu____16508 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16508))
          &&
          (let uu____16512 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16512)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16529 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16529 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16583 ->
        let uu____16598 =
          let uu____16600 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16600  in
        Prims.int_one + uu____16598
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16603 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16603
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16607 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16607
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16616 = sizeof t1  in (FStar_List.length us) + uu____16616
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16620) ->
        let uu____16645 = sizeof t1  in
        let uu____16647 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16662  ->
                 match uu____16662 with
                 | (bv,uu____16672) ->
                     let uu____16677 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16677) Prims.int_zero bs
           in
        uu____16645 + uu____16647
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____16706 = sizeof hd  in
        let uu____16708 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16723  ->
                 match uu____16723 with
                 | (arg,uu____16733) ->
                     let uu____16738 = sizeof arg  in acc + uu____16738)
            Prims.int_zero args
           in
        uu____16706 + uu____16708
    | uu____16741 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16755 =
        let uu____16756 = un_uinst t  in uu____16756.FStar_Syntax_Syntax.n
         in
      match uu____16755 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16761 -> false
  
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
           let uu____16822 = head_and_args t  in
           match uu____16822 with
           | (head,args) ->
               let uu____16877 =
                 let uu____16878 = FStar_Syntax_Subst.compress head  in
                 uu____16878.FStar_Syntax_Syntax.n  in
               (match uu____16877 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16904 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____16937 = is_fvar attr a  in Prims.op_Negation uu____16937)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      FStar_Errors.set_option_warning_callback_range
        (FStar_Pervasives_Native.Some r);
      (let set_options s =
         let uu____16959 = FStar_Options.set_options s  in
         match uu____16959 with
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
           ((let uu____16973 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____16973 (fun uu____16975  -> ()));
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
           let uu____16989 = FStar_Options.internal_pop ()  in
           if uu____16989
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
    | FStar_Syntax_Syntax.Tm_delayed uu____17021 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17040 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17055 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17056 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17057 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17066) ->
        let uu____17091 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17091 with
         | (bs1,t2) ->
             let uu____17100 =
               FStar_List.collect
                 (fun uu____17112  ->
                    match uu____17112 with
                    | (b,uu____17122) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17127 = unbound_variables t2  in
             FStar_List.append uu____17100 uu____17127)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17152 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17152 with
         | (bs1,c1) ->
             let uu____17161 =
               FStar_List.collect
                 (fun uu____17173  ->
                    match uu____17173 with
                    | (b,uu____17183) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17188 = unbound_variables_comp c1  in
             FStar_List.append uu____17161 uu____17188)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17197 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17197 with
         | (bs,t2) ->
             let uu____17220 =
               FStar_List.collect
                 (fun uu____17232  ->
                    match uu____17232 with
                    | (b1,uu____17242) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17247 = unbound_variables t2  in
             FStar_List.append uu____17220 uu____17247)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17276 =
          FStar_List.collect
            (fun uu____17290  ->
               match uu____17290 with
               | (x,uu____17302) -> unbound_variables x) args
           in
        let uu____17311 = unbound_variables t1  in
        FStar_List.append uu____17276 uu____17311
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17352 = unbound_variables t1  in
        let uu____17355 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17370 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17370 with
                  | (p,wopt,t2) ->
                      let uu____17392 = unbound_variables t2  in
                      let uu____17395 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17392 uu____17395))
           in
        FStar_List.append uu____17352 uu____17355
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17409) ->
        let uu____17450 = unbound_variables t1  in
        let uu____17453 =
          let uu____17456 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17487 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17456 uu____17487  in
        FStar_List.append uu____17450 uu____17453
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17528 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17531 =
          let uu____17534 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17537 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17542 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17544 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17544 with
                 | (uu____17565,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17534 uu____17537  in
        FStar_List.append uu____17528 uu____17531
    | FStar_Syntax_Syntax.Tm_let ((uu____17567,lbs),t1) ->
        let uu____17587 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17587 with
         | (lbs1,t2) ->
             let uu____17602 = unbound_variables t2  in
             let uu____17605 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17612 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17615 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17612 uu____17615) lbs1
                in
             FStar_List.append uu____17602 uu____17605)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17632 = unbound_variables t1  in
        let uu____17635 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17640,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17695  ->
                      match uu____17695 with
                      | (a,uu____17707) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17716,uu____17717,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17723,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17729 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17738 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17739 -> []  in
        FStar_List.append uu____17632 uu____17635

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17746) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17756) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17766 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17769 =
          FStar_List.collect
            (fun uu____17783  ->
               match uu____17783 with
               | (a,uu____17795) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17766 uu____17769

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
            let uu____17910 = head_and_args h  in
            (match uu____17910 with
             | (head,args) ->
                 let uu____17971 =
                   let uu____17972 = FStar_Syntax_Subst.compress head  in
                   uu____17972.FStar_Syntax_Syntax.n  in
                 (match uu____17971 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18025 -> aux (h :: acc) t))
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
      let uu____18049 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18049 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2475_18091 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2475_18091.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2475_18091.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2475_18091.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2475_18091.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2475_18091.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18099 =
      let uu____18100 = FStar_Syntax_Subst.compress t  in
      uu____18100.FStar_Syntax_Syntax.n  in
    match uu____18099 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18104,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18132)::uu____18133 ->
                  let pats' = unmeta pats  in
                  let uu____18193 = head_and_args pats'  in
                  (match uu____18193 with
                   | (head,uu____18212) ->
                       let uu____18237 =
                         let uu____18238 = un_uinst head  in
                         uu____18238.FStar_Syntax_Syntax.n  in
                       (match uu____18237 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18243 -> false))
              | uu____18245 -> false)
         | uu____18257 -> false)
    | uu____18259 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18275 =
      let uu____18292 = unmeta e  in head_and_args uu____18292  in
    match uu____18275 with
    | (head,args) ->
        let uu____18323 =
          let uu____18338 =
            let uu____18339 = un_uinst head  in
            uu____18339.FStar_Syntax_Syntax.n  in
          (uu____18338, args)  in
        (match uu____18323 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18357) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18381::(hd,uu____18383)::(tl,uu____18385)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18452 =
               let uu____18455 =
                 let uu____18458 = list_elements tl  in
                 FStar_Util.must uu____18458  in
               hd :: uu____18455  in
             FStar_Pervasives_Native.Some uu____18452
         | uu____18467 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18496 =
      let uu____18497 = FStar_Syntax_Subst.compress t  in
      uu____18497.FStar_Syntax_Syntax.n  in
    match uu____18496 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18504) ->
        let uu____18539 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18539 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18573 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18573
             then
               let uu____18580 =
                 let uu____18591 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18591]  in
               mk_app t uu____18580
             else e1)
    | uu____18618 ->
        let uu____18619 =
          let uu____18630 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18630]  in
        mk_app t uu____18619
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18685 = list_elements e  in
        match uu____18685 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18720 =
          let uu____18737 = unmeta p  in
          FStar_All.pipe_right uu____18737 head_and_args  in
        match uu____18720 with
        | (head,args) ->
            let uu____18788 =
              let uu____18803 =
                let uu____18804 = un_uinst head  in
                uu____18804.FStar_Syntax_Syntax.n  in
              (uu____18803, args)  in
            (match uu____18788 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____18826,uu____18827)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18879 ->
                 let uu____18894 =
                   let uu____18900 =
                     let uu____18902 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18902
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____18900)  in
                 FStar_Errors.raise_error uu____18894
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____18945 =
            let uu____18962 = unmeta t1  in
            FStar_All.pipe_right uu____18962 head_and_args  in
          match uu____18945 with
          | (head,args) ->
              let uu____19009 =
                let uu____19024 =
                  let uu____19025 = un_uinst head  in
                  uu____19025.FStar_Syntax_Syntax.n  in
                (uu____19024, args)  in
              (match uu____19009 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19044)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19081 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19111 = smt_pat_or t1  in
            (match uu____19111 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19133 = list_elements1 e  in
                 FStar_All.pipe_right uu____19133
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19163 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19163
                           (FStar_List.map one_pat)))
             | uu____19192 ->
                 let uu____19197 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19197])
        | uu____19252 ->
            let uu____19255 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19255]
         in
      let uu____19310 =
        let uu____19343 =
          let uu____19344 = FStar_Syntax_Subst.compress t  in
          uu____19344.FStar_Syntax_Syntax.n  in
        match uu____19343 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19401 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19401 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19472;
                        FStar_Syntax_Syntax.effect_name = uu____19473;
                        FStar_Syntax_Syntax.result_typ = uu____19474;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19476)::(post,uu____19478)::(pats,uu____19480)::[];
                        FStar_Syntax_Syntax.flags = uu____19481;_}
                      ->
                      let uu____19542 = lemma_pats pats  in
                      (binders1, pre, post, uu____19542)
                  | uu____19579 -> failwith "impos"))
        | uu____19613 -> failwith "Impos"  in
      match uu____19310 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19705 =
              let uu____19712 =
                let uu____19713 =
                  let uu____19720 = mk_imp pre post1  in
                  let uu____19723 =
                    let uu____19724 =
                      let uu____19745 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19745, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19724  in
                  (uu____19720, uu____19723)  in
                FStar_Syntax_Syntax.Tm_meta uu____19713  in
              FStar_Syntax_Syntax.mk uu____19712  in
            uu____19705 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19769 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19769 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19799 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19810 -> true
    | uu____19812 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____19823 -> true
    | uu____19825 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____19843 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____19844 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____19845 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____19846 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____19847 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____19848 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____19849 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____19850 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____19853 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____19856 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19843;
        FStar_Syntax_Syntax.bind_wp = uu____19844;
        FStar_Syntax_Syntax.stronger = uu____19845;
        FStar_Syntax_Syntax.if_then_else = uu____19846;
        FStar_Syntax_Syntax.ite_wp = uu____19847;
        FStar_Syntax_Syntax.close_wp = uu____19848;
        FStar_Syntax_Syntax.trivial = uu____19849;
        FStar_Syntax_Syntax.repr = uu____19850;
        FStar_Syntax_Syntax.return_repr = uu____19853;
        FStar_Syntax_Syntax.bind_repr = uu____19856
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____19888 =
        match uu____19888 with
        | (ts1,ts2) ->
            let uu____19899 = f ts1  in
            let uu____19900 = f ts2  in (uu____19899, uu____19900)
         in
      let uu____19901 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____19906 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____19911 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____19916 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____19921 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____19901;
        FStar_Syntax_Syntax.l_return = uu____19906;
        FStar_Syntax_Syntax.l_bind = uu____19911;
        FStar_Syntax_Syntax.l_subcomp = uu____19916;
        FStar_Syntax_Syntax.l_if_then_else = uu____19921
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
          let uu____19943 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____19943
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19945 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____19945
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19947 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____19947
  
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
    | uu____19962 -> FStar_Pervasives_Native.None
  
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
        let uu____19976 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____19976
          (fun uu____19983  -> FStar_Pervasives_Native.Some uu____19983)
  
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
        let uu____20023 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20023
          (fun uu____20030  -> FStar_Pervasives_Native.Some uu____20030)
  
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
        let uu____20044 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20044
          (fun uu____20051  -> FStar_Pervasives_Native.Some uu____20051)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20065  -> FStar_Pervasives_Native.Some uu____20065)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20069  -> FStar_Pervasives_Native.Some uu____20069)
    | uu____20070 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20082 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20082
          (fun uu____20089  -> FStar_Pervasives_Native.Some uu____20089)
    | uu____20090 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20104  -> FStar_Pervasives_Native.Some uu____20104)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20108  -> FStar_Pervasives_Native.Some uu____20108)
    | uu____20109 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20123  -> FStar_Pervasives_Native.Some uu____20123)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20127  -> FStar_Pervasives_Native.Some uu____20127)
    | uu____20128 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20152 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20153 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20155 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20155
          (fun uu____20162  -> FStar_Pervasives_Native.Some uu____20162)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun uu____20176  -> FStar_Pervasives_Native.Some uu____20176)
    | uu____20177 -> FStar_Pervasives_Native.None
  