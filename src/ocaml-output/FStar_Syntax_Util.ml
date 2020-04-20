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
  
let (effect_indices_from_repr :
  FStar_Syntax_Syntax.term ->
    Prims.bool ->
      FStar_Range.range ->
        Prims.string -> FStar_Syntax_Syntax.term Prims.list)
  =
  fun repr  ->
    fun is_layered  ->
      fun r  ->
        fun err  ->
          let err1 uu____1656 =
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEffect, err) r
             in
          let repr1 = FStar_Syntax_Subst.compress repr  in
          if is_layered
          then
            match repr1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_app (uu____1666,uu____1667::is) ->
                FStar_All.pipe_right is
                  (FStar_List.map FStar_Pervasives_Native.fst)
            | uu____1735 -> err1 ()
          else
            (match repr1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_arrow (uu____1740,c) ->
                 let uu____1762 = FStar_All.pipe_right c comp_to_comp_typ  in
                 FStar_All.pipe_right uu____1762
                   (fun ct  ->
                      FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                        (FStar_List.map FStar_Pervasives_Native.fst))
             | uu____1797 -> err1 ())
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1818)::[] -> wp
      | uu____1843 ->
          let uu____1854 =
            let uu____1856 =
              FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name  in
            let uu____1858 =
              let uu____1860 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length
                 in
              FStar_All.pipe_right uu____1860 FStar_Util.string_of_int  in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args"
              uu____1856 uu____1858
             in
          failwith uu____1854
       in
    let uu____1884 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1884, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1898 -> true
    | FStar_Syntax_Syntax.GTotal uu____1908 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1933  ->
               match uu___0_1933 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1937 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1954  ->
            match uu___1_1954 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1958 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1990 -> true
    | FStar_Syntax_Syntax.GTotal uu____2000 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_2015  ->
                   match uu___2_2015 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____2018 -> false)))
  
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
    let uu____2059 =
      let uu____2060 = FStar_Syntax_Subst.compress t  in
      uu____2060.FStar_Syntax_Syntax.n  in
    match uu____2059 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____2064,c) -> is_pure_or_ghost_comp c
    | uu____2086 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____2101 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2110 =
      let uu____2111 = FStar_Syntax_Subst.compress t  in
      uu____2111.FStar_Syntax_Syntax.n  in
    match uu____2110 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____2115,c) -> is_lemma_comp c
    | uu____2137 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2145 =
      let uu____2146 = FStar_Syntax_Subst.compress t  in
      uu____2146.FStar_Syntax_Syntax.n  in
    match uu____2145 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____2150) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____2176) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2213,t1,uu____2215) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2241,uu____2242) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2284) -> head_of t1
    | uu____2289 -> t
  
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
    | uu____2367 -> (t1, [])
  
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
        let uu____2449 = head_and_args' head  in
        (match uu____2449 with
         | (head1,args') -> (head1, (FStar_List.append args' args)))
    | uu____2518 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2545) ->
        FStar_Syntax_Subst.compress t2
    | uu____2550 -> t1
  
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
                (fun uu___3_2568  ->
                   match uu___3_2568 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2571 -> false)))
    | uu____2573 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2590) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2600) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2629 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2638 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___393_2650 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___393_2650.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___393_2650.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___393_2650.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___393_2650.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2666  ->
            match uu___4_2666 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2670 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2678 -> []
    | FStar_Syntax_Syntax.GTotal uu____2695 -> []
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
    | uu____2739 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2749,uu____2750) ->
        unascribe e2
    | uu____2791 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2844,uu____2845) ->
          ascribe t' k
      | uu____2886 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2913 =
      let uu____2922 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2922  in
    uu____2913 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2978 =
      let uu____2979 = FStar_Syntax_Subst.compress t  in
      uu____2979.FStar_Syntax_Syntax.n  in
    match uu____2978 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2983 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2983
    | uu____2984 -> t
  
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2991 =
      let uu____2992 = FStar_Syntax_Subst.compress t  in
      uu____2992.FStar_Syntax_Syntax.n  in
    match uu____2991 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2996 ->
             let uu____3005 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____3005
         | uu____3006 -> t)
    | uu____3007 -> t
  
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
      | uu____3032 -> false
  
let unlazy_as_t :
  'uuuuuu3045 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'uuuuuu3045
  =
  fun k  ->
    fun t  ->
      let uu____3056 =
        let uu____3057 = FStar_Syntax_Subst.compress t  in
        uu____3057.FStar_Syntax_Syntax.n  in
      match uu____3056 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____3062;
            FStar_Syntax_Syntax.rng = uu____3063;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____3066 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____3107 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____3107;
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
    let uu____3120 =
      let uu____3135 = unascribe t  in head_and_args' uu____3135  in
    match uu____3120 with
    | (hd,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____3169 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____3180 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____3191 -> false
  
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
      | (NotEqual ,uu____3241) -> NotEqual
      | (uu____3242,NotEqual ) -> NotEqual
      | (Unknown ,uu____3243) -> Unknown
      | (uu____3244,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___5_3353 = if uu___5_3353 then Equal else Unknown  in
      let equal_iff uu___6_3364 = if uu___6_3364 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____3385 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3407 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3407
        then
          let uu____3411 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3488  ->
                    match uu____3488 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3529 = eq_tm a1 a2  in
                        eq_inj acc uu____3529) Equal) uu____3411
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3543 =
          let uu____3560 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3560 head_and_args  in
        match uu____3543 with
        | (head1,args1) ->
            let uu____3613 =
              let uu____3630 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3630 head_and_args  in
            (match uu____3613 with
             | (head2,args2) ->
                 let uu____3683 =
                   let uu____3688 =
                     let uu____3689 = un_uinst head1  in
                     uu____3689.FStar_Syntax_Syntax.n  in
                   let uu____3692 =
                     let uu____3693 = un_uinst head2  in
                     uu____3693.FStar_Syntax_Syntax.n  in
                   (uu____3688, uu____3692)  in
                 (match uu____3683 with
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
                  | uu____3720 -> FStar_Pervasives_Native.None))
         in
      let t12 = unmeta t11  in
      let t22 = unmeta t21  in
      match ((t12.FStar_Syntax_Syntax.n), (t22.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3738,uu____3739) ->
          let uu____3740 = unlazy t12  in eq_tm uu____3740 t22
      | (uu____3741,FStar_Syntax_Syntax.Tm_lazy uu____3742) ->
          let uu____3743 = unlazy t22  in eq_tm t12 uu____3743
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          let uu____3746 = FStar_Syntax_Syntax.bv_eq a b  in
          equal_if uu____3746
      | uu____3748 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3772 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3772
            (fun uu____3820  ->
               match uu____3820 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3835 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3835
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3849 = eq_tm f g  in
          eq_and uu____3849
            (fun uu____3852  ->
               let uu____3853 = eq_univs_list us vs  in equal_if uu____3853)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3855),uu____3856) -> Unknown
      | (uu____3857,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3858)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3861 = FStar_Const.eq_const c d  in equal_iff uu____3861
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3864)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3866))) ->
          let uu____3895 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3895
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3949 =
            let uu____3954 =
              let uu____3955 = un_uinst h1  in
              uu____3955.FStar_Syntax_Syntax.n  in
            let uu____3958 =
              let uu____3959 = un_uinst h2  in
              uu____3959.FStar_Syntax_Syntax.n  in
            (uu____3954, uu____3958)  in
          (match uu____3949 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3965 =
                    let uu____3967 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3967  in
                  FStar_List.mem uu____3965 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3969 ->
               let uu____3974 = eq_tm h1 h2  in
               eq_and uu____3974 (fun uu____3976  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t13,bs1),FStar_Syntax_Syntax.Tm_match
         (t23,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____4082 = FStar_List.zip bs1 bs2  in
            let uu____4145 = eq_tm t13 t23  in
            FStar_List.fold_right
              (fun uu____4182  ->
                 fun a  ->
                   match uu____4182 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4275  -> branch_matches b1 b2))
              uu____4082 uu____4145
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v) ->
          let uu____4280 = eq_univs u v  in equal_if uu____4280
      | (FStar_Syntax_Syntax.Tm_quoted (t13,q1),FStar_Syntax_Syntax.Tm_quoted
         (t23,q2)) ->
          let uu____4294 = eq_quoteinfo q1 q2  in
          eq_and uu____4294 (fun uu____4296  -> eq_tm t13 t23)
      | (FStar_Syntax_Syntax.Tm_refine
         (t13,phi1),FStar_Syntax_Syntax.Tm_refine (t23,phi2)) ->
          let uu____4309 =
            eq_tm t13.FStar_Syntax_Syntax.sort t23.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4309 (fun uu____4311  -> eq_tm phi1 phi2)
      | uu____4312 -> Unknown

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
      | ([],uu____4384) -> NotEqual
      | (uu____4415,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          let uu____4504 =
            let uu____4506 = FStar_Syntax_Syntax.bv_eq x1 x2  in
            Prims.op_Negation uu____4506  in
          if uu____4504
          then NotEqual
          else
            (let uu____4511 = eq_tm t1 t2  in
             match uu____4511 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4512 = eq_antiquotes a11 a21  in
                 (match uu____4512 with
                  | NotEqual  -> NotEqual
                  | uu____4513 -> Unknown)
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
        | (uu____4597,uu____4598) -> false  in
      let uu____4608 = b1  in
      match uu____4608 with
      | (p1,w1,t1) ->
          let uu____4642 = b2  in
          (match uu____4642 with
           | (p2,w2,t2) ->
               let uu____4676 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4676
               then
                 let uu____4679 =
                   (let uu____4683 = eq_tm t1 t2  in uu____4683 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4692 = eq_tm t11 t21  in
                             uu____4692 = Equal) w1 w2)
                    in
                 (if uu____4679 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4757)::a11,(b,uu____4760)::b1) ->
          let uu____4834 = eq_tm a b  in
          (match uu____4834 with
           | Equal  -> eq_args a11 b1
           | uu____4835 -> Unknown)
      | uu____4836 -> Unknown

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
      | (FStar_Pervasives_Native.None ,uu____4891) -> NotEqual
      | (uu____4898,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4928 -> NotEqual
  
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4945) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4951,uu____4952) ->
        unrefine t2
    | uu____4993 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5001 =
      let uu____5002 = FStar_Syntax_Subst.compress t  in
      uu____5002.FStar_Syntax_Syntax.n  in
    match uu____5001 with
    | FStar_Syntax_Syntax.Tm_uvar uu____5006 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5021) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____5026 ->
        let uu____5043 =
          let uu____5044 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____5044 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____5043 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____5107,uu____5108) ->
        is_uvar t1
    | uu____5149 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5158 =
      let uu____5159 = unrefine t  in uu____5159.FStar_Syntax_Syntax.n  in
    match uu____5158 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head,uu____5165) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5191) -> is_unit t1
    | uu____5196 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5205 =
      let uu____5206 = FStar_Syntax_Subst.compress t  in
      uu____5206.FStar_Syntax_Syntax.n  in
    match uu____5205 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5211 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5220 =
      let uu____5221 = FStar_Syntax_Subst.compress e  in
      uu____5221.FStar_Syntax_Syntax.n  in
    match uu____5220 with
    | FStar_Syntax_Syntax.Tm_abs uu____5225 -> true
    | uu____5245 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5254 =
      let uu____5255 = FStar_Syntax_Subst.compress t  in
      uu____5255.FStar_Syntax_Syntax.n  in
    match uu____5254 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5259 -> true
    | uu____5275 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5285) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5291,uu____5292) ->
        pre_typ t2
    | uu____5333 -> t1
  
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
      let uu____5358 =
        let uu____5359 = un_uinst typ1  in uu____5359.FStar_Syntax_Syntax.n
         in
      match uu____5358 with
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let head1 = un_uinst head  in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5424 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5454 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5475,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5482) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5487,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5498,uu____5499,uu____5500,uu____5501,uu____5502) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5512,uu____5513,uu____5514,uu____5515) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5521,uu____5522,uu____5523,uu____5524,uu____5525) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5533,uu____5534) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5536,uu____5537) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5539 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5540 -> []
    | FStar_Syntax_Syntax.Sig_main uu____5541 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5542 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5555 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____5566 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5588 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5614  ->
    match uu___7_5614 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'uuuuuu5628 'uuuuuu5629 .
    ('uuuuuu5628 FStar_Syntax_Syntax.syntax * 'uuuuuu5629) ->
      FStar_Range.range
  =
  fun uu____5640  ->
    match uu____5640 with | (hd,uu____5648) -> hd.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'uuuuuu5662 'uuuuuu5663 .
    ('uuuuuu5662 FStar_Syntax_Syntax.syntax * 'uuuuuu5663) Prims.list ->
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
      | uu____5761 ->
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
      let uu____5820 =
        FStar_List.map
          (fun uu____5847  ->
             match uu____5847 with
             | (bv,aq) ->
                 let uu____5866 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5866, aq)) bs
         in
      mk_app f uu____5820
  
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
          (let uu____5917 =
             let uu____5923 =
               let uu____5925 =
                 let uu____5927 = FStar_Ident.ident_of_lid lid  in
                 FStar_Ident.text_of_id uu____5927  in
               mk_field_projector_name_from_string uu____5925 itext  in
             let uu____5928 = FStar_Ident.range_of_id i  in
             (uu____5923, uu____5928)  in
           FStar_Ident.mk_ident uu____5917)
         in
      let uu____5930 =
        let uu____5931 = FStar_Ident.ns_of_lid lid  in
        FStar_List.append uu____5931 [newi]  in
      FStar_Ident.lid_of_ids uu____5930
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5953 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5953
          then
            let uu____5956 =
              let uu____5962 =
                let uu____5964 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5964  in
              let uu____5967 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5962, uu____5967)  in
            FStar_Ident.mk_ident uu____5956
          else x.FStar_Syntax_Syntax.ppname  in
        mk_field_projector_name_from_ident lid nm
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5982) -> ses
    | uu____5991 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____6006 = FStar_Syntax_Unionfind.find uv  in
      match uu____6006 with
      | FStar_Pervasives_Native.Some uu____6009 ->
          let uu____6010 =
            let uu____6012 =
              let uu____6014 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____6014  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____6012  in
          failwith uu____6010
      | uu____6019 -> FStar_Syntax_Unionfind.change uv t
  
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
            (let uu____6043 = FStar_Ident.text_of_id l1b  in
             let uu____6045 = FStar_Ident.text_of_id l2b  in
             uu____6043 = uu____6045)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____6074 = FStar_Ident.text_of_id x1  in
                      let uu____6076 = FStar_Ident.text_of_id x2  in
                      uu____6074 = uu____6076) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____6085 = FStar_Ident.text_of_id x1  in
                    let uu____6087 = FStar_Ident.text_of_id x2  in
                    uu____6085 = uu____6087) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____6116 = FStar_Ident.text_of_id x1  in
                      let uu____6118 = FStar_Ident.text_of_id x2  in
                      uu____6116 = uu____6118) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____6127 = FStar_Ident.text_of_id x1  in
                    let uu____6129 = FStar_Ident.text_of_id x2  in
                    uu____6127 = uu____6129) f1 f2)
      | uu____6132 -> q1 = q2
  
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
              let uu____6178 =
                let uu___1025_6179 = rc  in
                let uu____6180 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1025_6179.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6180;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1025_6179.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6178
           in
        match bs with
        | [] -> t
        | uu____6197 ->
            let body =
              let uu____6199 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6199  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6229 =
                   let uu____6236 =
                     let uu____6237 =
                       let uu____6256 =
                         let uu____6265 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6265 bs'  in
                       let uu____6280 = close_lopt lopt'  in
                       (uu____6256, t1, uu____6280)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6237  in
                   FStar_Syntax_Syntax.mk uu____6236  in
                 uu____6229 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6295 ->
                 let uu____6296 =
                   let uu____6303 =
                     let uu____6304 =
                       let uu____6323 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6332 = close_lopt lopt  in
                       (uu____6323, body, uu____6332)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6304  in
                   FStar_Syntax_Syntax.mk uu____6303  in
                 uu____6296 FStar_Pervasives_Native.None
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
      | uu____6388 ->
          let uu____6397 =
            let uu____6404 =
              let uu____6405 =
                let uu____6420 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6429 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6420, uu____6429)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6405  in
            FStar_Syntax_Syntax.mk uu____6404  in
          uu____6397 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6478 =
        let uu____6479 = FStar_Syntax_Subst.compress t  in
        uu____6479.FStar_Syntax_Syntax.n  in
      match uu____6478 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6509) ->
               let uu____6518 =
                 let uu____6519 = FStar_Syntax_Subst.compress tres  in
                 uu____6519.FStar_Syntax_Syntax.n  in
               (match uu____6518 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6562 -> t)
           | uu____6563 -> t)
      | uu____6564 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6582 =
        let uu____6583 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6583 t.FStar_Syntax_Syntax.pos  in
      let uu____6584 =
        let uu____6591 =
          let uu____6592 =
            let uu____6599 =
              let uu____6602 =
                let uu____6603 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6603]  in
              FStar_Syntax_Subst.close uu____6602 t  in
            (b, uu____6599)  in
          FStar_Syntax_Syntax.Tm_refine uu____6592  in
        FStar_Syntax_Syntax.mk uu____6591  in
      uu____6584 FStar_Pervasives_Native.None uu____6582
  
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
        let uu____6683 = is_total_comp c  in
        if uu____6683
        then
          let uu____6698 = arrow_formals_comp_ln (comp_result c)  in
          (match uu____6698 with
           | (bs',k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6765;
           FStar_Syntax_Syntax.index = uu____6766;
           FStar_Syntax_Syntax.sort = s;_},uu____6768)
        ->
        let rec aux s1 k2 =
          let uu____6799 =
            let uu____6800 = FStar_Syntax_Subst.compress s1  in
            uu____6800.FStar_Syntax_Syntax.n  in
          match uu____6799 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6815 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6830;
                 FStar_Syntax_Syntax.index = uu____6831;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6833)
              -> aux s2 k2
          | uu____6841 ->
              let uu____6842 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6842)
           in
        aux s k1
    | uu____6857 ->
        let uu____6858 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6858)
  
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let uu____6883 = arrow_formals_comp_ln k  in
    match uu____6883 with | (bs,c) -> FStar_Syntax_Subst.open_comp bs c
  
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6938 = arrow_formals_comp_ln k  in
    match uu____6938 with | (bs,c) -> (bs, (comp_result c))
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____7005 = arrow_formals_comp k  in
    match uu____7005 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7107 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7107 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____7131 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_7140  ->
                         match uu___8_7140 with
                         | FStar_Syntax_Syntax.DECREASES uu____7142 -> true
                         | uu____7146 -> false))
                  in
               (match uu____7131 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7181 ->
                    let uu____7184 = is_total_comp c1  in
                    if uu____7184
                    then
                      let uu____7203 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7203 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7296;
             FStar_Syntax_Syntax.index = uu____7297;
             FStar_Syntax_Syntax.sort = k2;_},uu____7299)
          -> arrow_until_decreases k2
      | uu____7307 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7328 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7328 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7382 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7403 =
                 FStar_Common.tabulate n_univs (fun uu____7409  -> false)  in
               let uu____7412 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7437  ->
                         match uu____7437 with
                         | (x,uu____7446) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7403 uu____7412)
           in
        ((n_univs + (FStar_List.length bs)), uu____7382)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7502 =
            let uu___1152_7503 = rc  in
            let uu____7504 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1152_7503.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7504;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1152_7503.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7502
      | uu____7513 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7547 =
        let uu____7548 =
          let uu____7551 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7551  in
        uu____7548.FStar_Syntax_Syntax.n  in
      match uu____7547 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7597 = aux t2 what  in
          (match uu____7597 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7669 -> ([], t1, abs_body_lcomp)  in
    let uu____7686 = aux t FStar_Pervasives_Native.None  in
    match uu____7686 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7734 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7734 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let no_acc uu____7768 =
      match uu____7768 with
      | (b,aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true )) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7782 -> aq  in
          (b, aq1)
       in
    let uu____7787 = arrow_formals_comp_ln t  in
    match uu____7787 with
    | (bs,c) ->
        (match bs with
         | [] -> t
         | uu____7824 ->
             let uu____7833 =
               let uu____7840 =
                 let uu____7841 =
                   let uu____7856 = FStar_List.map no_acc bs  in
                   (uu____7856, c)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____7841  in
               FStar_Syntax_Syntax.mk uu____7840  in
             uu____7833 FStar_Pervasives_Native.None
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
                    | (FStar_Pervasives_Native.None ,uu____8027) -> def
                    | (uu____8038,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____8050) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu____8066  ->
                                  FStar_Syntax_Syntax.U_name uu____8066))
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
            let uu____8148 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____8148 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____8183 ->
            let t' = arrow binders c  in
            let uu____8195 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____8195 with
             | (uvs1,t'1) ->
                 let uu____8216 =
                   let uu____8217 = FStar_Syntax_Subst.compress t'1  in
                   uu____8217.FStar_Syntax_Syntax.n  in
                 (match uu____8216 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8266 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8291 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Parser_Const.is_tuple_constructor_string uu____8291
    | uu____8293 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8304 -> false
  
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
      let uu____8367 =
        let uu____8368 = pre_typ t  in uu____8368.FStar_Syntax_Syntax.n  in
      match uu____8367 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8373 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8387 =
        let uu____8388 = pre_typ t  in uu____8388.FStar_Syntax_Syntax.n  in
      match uu____8387 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8392 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8394) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8420) ->
          is_constructed_typ t1 lid
      | uu____8425 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8438 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8439 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8440 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8442) -> get_tycon t2
    | uu____8467 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8475 =
      let uu____8476 = un_uinst t  in uu____8476.FStar_Syntax_Syntax.n  in
    match uu____8475 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8481 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8495 =
        let uu____8499 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8499  in
      match uu____8495 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8531 -> false
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
  fun uu____8550  ->
    let u =
      let uu____8556 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left
        (fun uu____8573  -> FStar_Syntax_Syntax.U_unif uu____8573) uu____8556
       in
    let uu____8574 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8574, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8587 = eq_tm a a'  in
      match uu____8587 with | Equal  -> true | uu____8590 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8595 =
    let uu____8602 =
      let uu____8603 =
        let uu____8604 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8604
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8603  in
    FStar_Syntax_Syntax.mk uu____8602  in
  uu____8595 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8717 =
            let uu____8720 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8721 =
              let uu____8728 =
                let uu____8729 =
                  let uu____8746 =
                    let uu____8757 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8766 =
                      let uu____8777 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8777]  in
                    uu____8757 :: uu____8766  in
                  (tand, uu____8746)  in
                FStar_Syntax_Syntax.Tm_app uu____8729  in
              FStar_Syntax_Syntax.mk uu____8728  in
            uu____8721 FStar_Pervasives_Native.None uu____8720  in
          FStar_Pervasives_Native.Some uu____8717
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8854 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8855 =
          let uu____8862 =
            let uu____8863 =
              let uu____8880 =
                let uu____8891 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8900 =
                  let uu____8911 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8911]  in
                uu____8891 :: uu____8900  in
              (op_t, uu____8880)  in
            FStar_Syntax_Syntax.Tm_app uu____8863  in
          FStar_Syntax_Syntax.mk uu____8862  in
        uu____8855 FStar_Pervasives_Native.None uu____8854
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8968 =
      let uu____8975 =
        let uu____8976 =
          let uu____8993 =
            let uu____9004 = FStar_Syntax_Syntax.as_arg phi  in [uu____9004]
             in
          (t_not, uu____8993)  in
        FStar_Syntax_Syntax.Tm_app uu____8976  in
      FStar_Syntax_Syntax.mk uu____8975  in
    uu____8968 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____9201 =
      let uu____9208 =
        let uu____9209 =
          let uu____9226 =
            let uu____9237 = FStar_Syntax_Syntax.as_arg e  in [uu____9237]
             in
          (b2t_v, uu____9226)  in
        FStar_Syntax_Syntax.Tm_app uu____9209  in
      FStar_Syntax_Syntax.mk uu____9208  in
    uu____9201 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9284 = head_and_args e  in
    match uu____9284 with
    | (hd,args) ->
        let uu____9329 =
          let uu____9344 =
            let uu____9345 = FStar_Syntax_Subst.compress hd  in
            uu____9345.FStar_Syntax_Syntax.n  in
          (uu____9344, args)  in
        (match uu____9329 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9362)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9397 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9419 =
      let uu____9420 = unmeta t  in uu____9420.FStar_Syntax_Syntax.n  in
    match uu____9419 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9425 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9448 = is_t_true t1  in
      if uu____9448
      then t2
      else
        (let uu____9455 = is_t_true t2  in
         if uu____9455 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9483 = is_t_true t1  in
      if uu____9483
      then t_true
      else
        (let uu____9490 = is_t_true t2  in
         if uu____9490 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9519 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9520 =
        let uu____9527 =
          let uu____9528 =
            let uu____9545 =
              let uu____9556 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9565 =
                let uu____9576 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9576]  in
              uu____9556 :: uu____9565  in
            (teq, uu____9545)  in
          FStar_Syntax_Syntax.Tm_app uu____9528  in
        FStar_Syntax_Syntax.mk uu____9527  in
      uu____9520 FStar_Pervasives_Native.None uu____9519
  
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
          let uu____9643 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9644 =
            let uu____9651 =
              let uu____9652 =
                let uu____9669 =
                  let uu____9680 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9689 =
                    let uu____9700 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9709 =
                      let uu____9720 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9720]  in
                    uu____9700 :: uu____9709  in
                  uu____9680 :: uu____9689  in
                (eq_inst, uu____9669)  in
              FStar_Syntax_Syntax.Tm_app uu____9652  in
            FStar_Syntax_Syntax.mk uu____9651  in
          uu____9644 FStar_Pervasives_Native.None uu____9643
  
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
        let uu____9797 =
          let uu____9804 =
            let uu____9805 =
              let uu____9822 =
                let uu____9833 = FStar_Syntax_Syntax.iarg t  in
                let uu____9842 =
                  let uu____9853 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9862 =
                    let uu____9873 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9873]  in
                  uu____9853 :: uu____9862  in
                uu____9833 :: uu____9842  in
              (t_has_type1, uu____9822)  in
            FStar_Syntax_Syntax.Tm_app uu____9805  in
          FStar_Syntax_Syntax.mk uu____9804  in
        uu____9797 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9950 =
          let uu____9957 =
            let uu____9958 =
              let uu____9975 =
                let uu____9986 = FStar_Syntax_Syntax.iarg t  in
                let uu____9995 =
                  let uu____10006 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____10006]  in
                uu____9986 :: uu____9995  in
              (t_with_type1, uu____9975)  in
            FStar_Syntax_Syntax.Tm_app uu____9958  in
          FStar_Syntax_Syntax.mk uu____9957  in
        uu____9950 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____10053 =
    let uu____10060 =
      let uu____10061 =
        let uu____10068 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____10068, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____10061  in
    FStar_Syntax_Syntax.mk uu____10060  in
  uu____10053 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
        let uu____10151 =
          let uu____10158 =
            let uu____10159 =
              let uu____10176 =
                let uu____10187 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____10196 =
                  let uu____10207 =
                    let uu____10216 =
                      let uu____10217 =
                        let uu____10218 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10218]  in
                      abs uu____10217 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10216  in
                  [uu____10207]  in
                uu____10187 :: uu____10196  in
              (fa, uu____10176)  in
            FStar_Syntax_Syntax.Tm_app uu____10159  in
          FStar_Syntax_Syntax.mk uu____10158  in
        uu____10151 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10345 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10345
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10364 -> true
    | uu____10366 -> false
  
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
          let uu____10413 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10413, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10442 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10442, FStar_Pervasives_Native.None, t2)  in
        let uu____10456 =
          let uu____10457 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10457  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10456
  
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
      let uu____10533 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10536 =
        let uu____10547 = FStar_Syntax_Syntax.as_arg p  in [uu____10547]  in
      mk_app uu____10533 uu____10536
  
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
      let uu____10587 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10590 =
        let uu____10601 = FStar_Syntax_Syntax.as_arg p  in [uu____10601]  in
      mk_app uu____10587 uu____10590
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10636 = head_and_args t  in
    match uu____10636 with
    | (head,args) ->
        let head1 = unascribe head  in
        let head2 = un_uinst head1  in
        let uu____10685 =
          let uu____10700 =
            let uu____10701 = FStar_Syntax_Subst.compress head2  in
            uu____10701.FStar_Syntax_Syntax.n  in
          (uu____10700, args)  in
        (match uu____10685 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10720)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10786 =
                    let uu____10791 =
                      let uu____10792 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10792]  in
                    FStar_Syntax_Subst.open_term uu____10791 p  in
                  (match uu____10786 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10849 -> failwith "impossible"  in
                       let uu____10857 =
                         let uu____10859 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10859
                          in
                       if uu____10857
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10875 -> FStar_Pervasives_Native.None)
         | uu____10878 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10909 = head_and_args t  in
    match uu____10909 with
    | (head,args) ->
        let uu____10960 =
          let uu____10975 =
            let uu____10976 = FStar_Syntax_Subst.compress head  in
            uu____10976.FStar_Syntax_Syntax.n  in
          (uu____10975, args)  in
        (match uu____10960 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10998;
               FStar_Syntax_Syntax.vars = uu____10999;_},u::[]),(t1,uu____11002)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11049 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11084 = head_and_args t  in
    match uu____11084 with
    | (head,args) ->
        let uu____11135 =
          let uu____11150 =
            let uu____11151 = FStar_Syntax_Subst.compress head  in
            uu____11151.FStar_Syntax_Syntax.n  in
          (uu____11150, args)  in
        (match uu____11135 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____11173;
               FStar_Syntax_Syntax.vars = uu____11174;_},u::[]),(t1,uu____11177)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11224 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11252 =
      let uu____11269 = unmeta t  in head_and_args uu____11269  in
    match uu____11252 with
    | (head,uu____11272) ->
        let uu____11297 =
          let uu____11298 = un_uinst head  in
          uu____11298.FStar_Syntax_Syntax.n  in
        (match uu____11297 with
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
         | uu____11303 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11323 =
      let uu____11324 = FStar_Syntax_Subst.compress t  in
      uu____11324.FStar_Syntax_Syntax.n  in
    match uu____11323 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11430 =
          let uu____11435 =
            let uu____11436 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11436  in
          (b, uu____11435)  in
        FStar_Pervasives_Native.Some uu____11430
    | uu____11441 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11464 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11464
      (fun uu____11492  ->
         match uu____11492 with
         | (b,c) ->
             let uu____11511 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11511 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11574 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11611 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11611
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11663 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11706 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11747 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____12133) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____12145) ->
          unmeta_monadic t
      | uu____12158 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12227 =
        match uu____12227 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12265  ->
                   match uu____12265 with
                   | (lid,out_lid) ->
                       let uu____12274 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12274
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12301 = head_and_args t  in
      match uu____12301 with
      | (hd,args) ->
          let uu____12346 =
            let uu____12347 = un_uinst hd  in
            uu____12347.FStar_Syntax_Syntax.n  in
          (match uu____12346 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12353 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12362 = un_squash t  in
      FStar_Util.bind_opt uu____12362
        (fun t1  ->
           let uu____12378 = head_and_args' t1  in
           match uu____12378 with
           | (hd,args) ->
               let uu____12417 =
                 let uu____12418 = un_uinst hd  in
                 uu____12418.FStar_Syntax_Syntax.n  in
               (match uu____12417 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12424 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12465,pats)) ->
          let uu____12503 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12503)
      | uu____12516 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12583 = head_and_args t1  in
        match uu____12583 with
        | (t2,args) ->
            let uu____12638 = un_uinst t2  in
            let uu____12639 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12680  ->
                      match uu____12680 with
                      | (t3,imp) ->
                          let uu____12699 = unascribe t3  in
                          (uu____12699, imp)))
               in
            (uu____12638, uu____12639)
         in
      let rec aux qopt out t1 =
        let uu____12750 = let uu____12774 = flat t1  in (qopt, uu____12774)
           in
        match uu____12750 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12814;
                 FStar_Syntax_Syntax.vars = uu____12815;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12818);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12819;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12820;_},uu____12821)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12923;
                 FStar_Syntax_Syntax.vars = uu____12924;_},uu____12925::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12928);
                  FStar_Syntax_Syntax.pos = uu____12929;
                  FStar_Syntax_Syntax.vars = uu____12930;_},uu____12931)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13048;
               FStar_Syntax_Syntax.vars = uu____13049;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____13052);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____13053;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____13054;_},uu____13055)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13148 =
              let uu____13152 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13152  in
            aux uu____13148 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13162;
               FStar_Syntax_Syntax.vars = uu____13163;_},uu____13164::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____13167);
                FStar_Syntax_Syntax.pos = uu____13168;
                FStar_Syntax_Syntax.vars = uu____13169;_},uu____13170)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13279 =
              let uu____13283 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13283  in
            aux uu____13279 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13293) ->
            let bs = FStar_List.rev out  in
            let uu____13346 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13346 with
             | (bs1,t2) ->
                 let uu____13355 = patterns t2  in
                 (match uu____13355 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13405 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13460 = un_squash t  in
      FStar_Util.bind_opt uu____13460
        (fun t1  ->
           let uu____13475 = arrow_one t1  in
           match uu____13475 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13490 =
                 let uu____13492 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13492  in
               if uu____13490
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13502 = comp_to_comp_typ_nouniv c  in
                    uu____13502.FStar_Syntax_Syntax.result_typ  in
                  let uu____13503 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13503
                  then
                    let uu____13510 = patterns q  in
                    match uu____13510 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13573 =
                       let uu____13574 =
                         let uu____13579 =
                           let uu____13580 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13591 =
                             let uu____13602 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13602]  in
                           uu____13580 :: uu____13591  in
                         (FStar_Parser_Const.imp_lid, uu____13579)  in
                       BaseConn uu____13574  in
                     FStar_Pervasives_Native.Some uu____13573))
           | uu____13635 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13643 = un_squash t  in
      FStar_Util.bind_opt uu____13643
        (fun t1  ->
           let uu____13674 = head_and_args' t1  in
           match uu____13674 with
           | (hd,args) ->
               let uu____13713 =
                 let uu____13728 =
                   let uu____13729 = un_uinst hd  in
                   uu____13729.FStar_Syntax_Syntax.n  in
                 (uu____13728, args)  in
               (match uu____13713 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13746)::(a2,uu____13748)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13799 =
                      let uu____13800 = FStar_Syntax_Subst.compress a2  in
                      uu____13800.FStar_Syntax_Syntax.n  in
                    (match uu____13799 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13807) ->
                         let uu____13842 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13842 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13895 -> failwith "impossible"  in
                              let uu____13903 = patterns q1  in
                              (match uu____13903 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13964 -> FStar_Pervasives_Native.None)
                | uu____13965 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____13988 = destruct_sq_forall phi  in
          (match uu____13988 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____13998  ->
                    FStar_Pervasives_Native.Some uu____13998)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____14005 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____14011 = destruct_sq_exists phi  in
          (match uu____14011 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____14021  ->
                    FStar_Pervasives_Native.Some uu____14021)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____14028 -> f1)
      | uu____14031 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____14035 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____14035
      (fun uu____14040  ->
         let uu____14041 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____14041
           (fun uu____14046  ->
              let uu____14047 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____14047
                (fun uu____14052  ->
                   let uu____14053 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____14053
                     (fun uu____14058  ->
                        let uu____14059 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____14059
                          (fun uu____14063  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____14081 =
            let uu____14086 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____14086  in
          let uu____14087 =
            let uu____14088 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____14088  in
          let uu____14091 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____14081 a.FStar_Syntax_Syntax.action_univs uu____14087
            FStar_Parser_Const.effect_Tot_lid uu____14091 [] pos
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
    let uu____14117 =
      let uu____14124 =
        let uu____14125 =
          let uu____14142 =
            let uu____14153 = FStar_Syntax_Syntax.as_arg t  in [uu____14153]
             in
          (reify_, uu____14142)  in
        FStar_Syntax_Syntax.Tm_app uu____14125  in
      FStar_Syntax_Syntax.mk uu____14124  in
    uu____14117 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14205 =
        let uu____14212 =
          let uu____14213 =
            let uu____14214 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14214  in
          FStar_Syntax_Syntax.Tm_constant uu____14213  in
        FStar_Syntax_Syntax.mk uu____14212  in
      uu____14205 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14216 =
      let uu____14223 =
        let uu____14224 =
          let uu____14241 =
            let uu____14252 = FStar_Syntax_Syntax.as_arg t  in [uu____14252]
             in
          (reflect_, uu____14241)  in
        FStar_Syntax_Syntax.Tm_app uu____14224  in
      FStar_Syntax_Syntax.mk uu____14223  in
    uu____14216 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14296 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14313 = unfold_lazy i  in delta_qualifier uu____14313
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14315 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14316 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14317 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14340 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14353 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14354 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14361 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14362 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14378) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14383;
           FStar_Syntax_Syntax.index = uu____14384;
           FStar_Syntax_Syntax.sort = t2;_},uu____14386)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14395) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14401,uu____14402) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14444) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14469,t2,uu____14471) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14496,t2) -> delta_qualifier t2
  
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
    let uu____14535 = delta_qualifier t  in incr_delta_depth uu____14535
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14543 =
      let uu____14544 = FStar_Syntax_Subst.compress t  in
      uu____14544.FStar_Syntax_Syntax.n  in
    match uu____14543 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14549 -> false
  
let rec apply_last :
  'uuuuuu14558 .
    ('uuuuuu14558 -> 'uuuuuu14558) ->
      'uuuuuu14558 Prims.list -> 'uuuuuu14558 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14584 = f a  in [uu____14584]
      | x::xs -> let uu____14589 = apply_last f xs  in x :: uu____14589
  
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
          let uu____14644 =
            let uu____14651 =
              let uu____14652 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14652  in
            FStar_Syntax_Syntax.mk uu____14651  in
          uu____14644 FStar_Pervasives_Native.None rng  in
        let cons args pos =
          let uu____14666 =
            let uu____14671 =
              let uu____14672 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14672
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14671 args  in
          uu____14666 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14686 =
            let uu____14691 =
              let uu____14692 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14692
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14691 args  in
          uu____14686 FStar_Pervasives_Native.None pos  in
        let uu____14693 =
          let uu____14694 =
            let uu____14695 = FStar_Syntax_Syntax.iarg typ  in [uu____14695]
             in
          nil uu____14694 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14729 =
                 let uu____14730 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14739 =
                   let uu____14750 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14759 =
                     let uu____14770 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14770]  in
                   uu____14750 :: uu____14759  in
                 uu____14730 :: uu____14739  in
               cons uu____14729 t.FStar_Syntax_Syntax.pos) l uu____14693
  
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
        | uu____14879 -> false
  
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
          | uu____14993 -> false
  
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
        | uu____15159 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15197 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15197
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
        let t11 = let uu____15401 = unmeta_safe t1  in canon_app uu____15401
           in
        let t21 = let uu____15407 = unmeta_safe t2  in canon_app uu____15407
           in
        let uu____15410 =
          let uu____15415 =
            let uu____15416 =
              let uu____15419 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15419  in
            uu____15416.FStar_Syntax_Syntax.n  in
          let uu____15420 =
            let uu____15421 =
              let uu____15424 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15424  in
            uu____15421.FStar_Syntax_Syntax.n  in
          (uu____15415, uu____15420)  in
        match uu____15410 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15426,uu____15427) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15436,FStar_Syntax_Syntax.Tm_uinst uu____15437) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15446,uu____15447) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15464,FStar_Syntax_Syntax.Tm_delayed uu____15465) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15482,uu____15483) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15512,FStar_Syntax_Syntax.Tm_ascribed uu____15513) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15552 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15552
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15557 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15557
        | (FStar_Syntax_Syntax.Tm_type
           uu____15560,FStar_Syntax_Syntax.Tm_type uu____15561) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15619 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15619) &&
              (let uu____15629 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15629)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15678 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15678) &&
              (let uu____15688 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15688)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15705 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15705) &&
              (let uu____15709 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15709)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15766 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15766) &&
              (let uu____15770 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15770)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15859 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15859) &&
              (let uu____15863 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15863)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15880,uu____15881) ->
            let uu____15882 =
              let uu____15884 = unlazy t11  in
              term_eq_dbg dbg uu____15884 t21  in
            check "lazy_l" uu____15882
        | (uu____15886,FStar_Syntax_Syntax.Tm_lazy uu____15887) ->
            let uu____15888 =
              let uu____15890 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15890  in
            check "lazy_r" uu____15888
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15935 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15935))
              &&
              (let uu____15939 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15939)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15943),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15945)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____16003 =
               let uu____16005 = eq_quoteinfo qi1 qi2  in uu____16005 = Equal
                in
             check "tm_quoted qi" uu____16003) &&
              (let uu____16008 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____16008)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____16038 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____16038) &&
                   (let uu____16042 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____16042)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____16061 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____16061) &&
                    (let uu____16065 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____16065))
                   &&
                   (let uu____16069 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____16069)
             | uu____16072 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____16078) -> fail "unk"
        | (uu____16080,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____16082,uu____16083) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____16085,uu____16086) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____16088,uu____16089) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____16091,uu____16092) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____16094,uu____16095) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____16097,uu____16098) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____16118,uu____16119) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____16135,uu____16136) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____16144,uu____16145) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____16163,uu____16164) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16188,uu____16189) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16204,uu____16205) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16219,uu____16220) ->
            fail "bottom"
        | (uu____16228,FStar_Syntax_Syntax.Tm_bvar uu____16229) ->
            fail "bottom"
        | (uu____16231,FStar_Syntax_Syntax.Tm_name uu____16232) ->
            fail "bottom"
        | (uu____16234,FStar_Syntax_Syntax.Tm_fvar uu____16235) ->
            fail "bottom"
        | (uu____16237,FStar_Syntax_Syntax.Tm_constant uu____16238) ->
            fail "bottom"
        | (uu____16240,FStar_Syntax_Syntax.Tm_type uu____16241) ->
            fail "bottom"
        | (uu____16243,FStar_Syntax_Syntax.Tm_abs uu____16244) ->
            fail "bottom"
        | (uu____16264,FStar_Syntax_Syntax.Tm_arrow uu____16265) ->
            fail "bottom"
        | (uu____16281,FStar_Syntax_Syntax.Tm_refine uu____16282) ->
            fail "bottom"
        | (uu____16290,FStar_Syntax_Syntax.Tm_app uu____16291) ->
            fail "bottom"
        | (uu____16309,FStar_Syntax_Syntax.Tm_match uu____16310) ->
            fail "bottom"
        | (uu____16334,FStar_Syntax_Syntax.Tm_let uu____16335) ->
            fail "bottom"
        | (uu____16350,FStar_Syntax_Syntax.Tm_uvar uu____16351) ->
            fail "bottom"
        | (uu____16365,FStar_Syntax_Syntax.Tm_meta uu____16366) ->
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
               let uu____16401 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16401)
          (fun q1  ->
             fun q2  ->
               let uu____16413 =
                 let uu____16415 = eq_aqual q1 q2  in uu____16415 = Equal  in
               check "arg qual" uu____16413) a1 a2

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
               let uu____16440 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16440)
          (fun q1  ->
             fun q2  ->
               let uu____16452 =
                 let uu____16454 = eq_aqual q1 q2  in uu____16454 = Equal  in
               check "binder qual" uu____16452) b1 b2

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
        ((let uu____16468 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16468) &&
           (let uu____16472 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16472))
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
    fun uu____16482  ->
      fun uu____16483  ->
        match (uu____16482, uu____16483) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16610 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16610) &&
               (let uu____16614 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16614))
              &&
              (let uu____16618 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16660 -> false  in
               check "branch when" uu____16618)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16681 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16681) &&
           (let uu____16690 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16690))
          &&
          (let uu____16694 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16694)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16711 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16711 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16765 ->
        let uu____16780 =
          let uu____16782 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16782  in
        Prims.int_one + uu____16780
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16785 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16785
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16789 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16789
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16798 = sizeof t1  in (FStar_List.length us) + uu____16798
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16802) ->
        let uu____16827 = sizeof t1  in
        let uu____16829 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16844  ->
                 match uu____16844 with
                 | (bv,uu____16854) ->
                     let uu____16859 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16859) Prims.int_zero bs
           in
        uu____16827 + uu____16829
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____16888 = sizeof hd  in
        let uu____16890 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16905  ->
                 match uu____16905 with
                 | (arg,uu____16915) ->
                     let uu____16920 = sizeof arg  in acc + uu____16920)
            Prims.int_zero args
           in
        uu____16888 + uu____16890
    | uu____16923 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16937 =
        let uu____16938 = un_uinst t  in uu____16938.FStar_Syntax_Syntax.n
         in
      match uu____16937 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16943 -> false
  
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
           let uu____17004 = head_and_args t  in
           match uu____17004 with
           | (head,args) ->
               let uu____17059 =
                 let uu____17060 = FStar_Syntax_Subst.compress head  in
                 uu____17060.FStar_Syntax_Syntax.n  in
               (match uu____17059 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____17086 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____17119 = is_fvar attr a  in Prims.op_Negation uu____17119)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options s =
        let uu____17140 = FStar_Options.set_options s  in
        match uu____17140 with
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
          ((let uu____17154 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____17154 (fun uu____17156  -> ()));
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
          let uu____17170 = FStar_Options.internal_pop ()  in
          if uu____17170
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
    | FStar_Syntax_Syntax.Tm_delayed uu____17202 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17221 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17236 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17237 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17238 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17247) ->
        let uu____17272 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17272 with
         | (bs1,t2) ->
             let uu____17281 =
               FStar_List.collect
                 (fun uu____17293  ->
                    match uu____17293 with
                    | (b,uu____17303) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17308 = unbound_variables t2  in
             FStar_List.append uu____17281 uu____17308)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17333 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17333 with
         | (bs1,c1) ->
             let uu____17342 =
               FStar_List.collect
                 (fun uu____17354  ->
                    match uu____17354 with
                    | (b,uu____17364) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17369 = unbound_variables_comp c1  in
             FStar_List.append uu____17342 uu____17369)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17378 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17378 with
         | (bs,t2) ->
             let uu____17401 =
               FStar_List.collect
                 (fun uu____17413  ->
                    match uu____17413 with
                    | (b1,uu____17423) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17428 = unbound_variables t2  in
             FStar_List.append uu____17401 uu____17428)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17457 =
          FStar_List.collect
            (fun uu____17471  ->
               match uu____17471 with
               | (x,uu____17483) -> unbound_variables x) args
           in
        let uu____17492 = unbound_variables t1  in
        FStar_List.append uu____17457 uu____17492
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17533 = unbound_variables t1  in
        let uu____17536 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17551 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17551 with
                  | (p,wopt,t2) ->
                      let uu____17573 = unbound_variables t2  in
                      let uu____17576 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17573 uu____17576))
           in
        FStar_List.append uu____17533 uu____17536
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17590) ->
        let uu____17631 = unbound_variables t1  in
        let uu____17634 =
          let uu____17637 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17668 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17637 uu____17668  in
        FStar_List.append uu____17631 uu____17634
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17709 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17712 =
          let uu____17715 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17718 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17723 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17725 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17725 with
                 | (uu____17746,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17715 uu____17718  in
        FStar_List.append uu____17709 uu____17712
    | FStar_Syntax_Syntax.Tm_let ((uu____17748,lbs),t1) ->
        let uu____17768 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17768 with
         | (lbs1,t2) ->
             let uu____17783 = unbound_variables t2  in
             let uu____17786 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17793 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17796 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17793 uu____17796) lbs1
                in
             FStar_List.append uu____17783 uu____17786)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17813 = unbound_variables t1  in
        let uu____17816 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17821,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17876  ->
                      match uu____17876 with
                      | (a,uu____17888) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17897,uu____17898,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17904,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17910 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17919 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17920 -> []  in
        FStar_List.append uu____17813 uu____17816

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17927) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17937) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17947 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17950 =
          FStar_List.collect
            (fun uu____17964  ->
               match uu____17964 with
               | (a,uu____17976) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17947 uu____17950

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
            let uu____18091 = head_and_args h  in
            (match uu____18091 with
             | (head,args) ->
                 let uu____18152 =
                   let uu____18153 = FStar_Syntax_Subst.compress head  in
                   uu____18153.FStar_Syntax_Syntax.n  in
                 (match uu____18152 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18206 -> aux (h :: acc) t))
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
      let uu____18230 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18230 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2507_18272 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2507_18272.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2507_18272.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2507_18272.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2507_18272.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2507_18272.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18280 =
      let uu____18281 = FStar_Syntax_Subst.compress t  in
      uu____18281.FStar_Syntax_Syntax.n  in
    match uu____18280 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18285,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18313)::uu____18314 ->
                  let pats' = unmeta pats  in
                  let uu____18374 = head_and_args pats'  in
                  (match uu____18374 with
                   | (head,uu____18393) ->
                       let uu____18418 =
                         let uu____18419 = un_uinst head  in
                         uu____18419.FStar_Syntax_Syntax.n  in
                       (match uu____18418 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18424 -> false))
              | uu____18426 -> false)
         | uu____18438 -> false)
    | uu____18440 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18456 =
      let uu____18473 = unmeta e  in head_and_args uu____18473  in
    match uu____18456 with
    | (head,args) ->
        let uu____18504 =
          let uu____18519 =
            let uu____18520 = un_uinst head  in
            uu____18520.FStar_Syntax_Syntax.n  in
          (uu____18519, args)  in
        (match uu____18504 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18538) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18562::(hd,uu____18564)::(tl,uu____18566)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18633 =
               let uu____18636 =
                 let uu____18639 = list_elements tl  in
                 FStar_Util.must uu____18639  in
               hd :: uu____18636  in
             FStar_Pervasives_Native.Some uu____18633
         | uu____18648 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18677 =
      let uu____18678 = FStar_Syntax_Subst.compress t  in
      uu____18678.FStar_Syntax_Syntax.n  in
    match uu____18677 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18685) ->
        let uu____18720 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18720 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18754 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18754
             then
               let uu____18761 =
                 let uu____18772 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18772]  in
               mk_app t uu____18761
             else e1)
    | uu____18799 ->
        let uu____18800 =
          let uu____18811 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18811]  in
        mk_app t uu____18800
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18866 = list_elements e  in
        match uu____18866 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18901 =
          let uu____18918 = unmeta p  in
          FStar_All.pipe_right uu____18918 head_and_args  in
        match uu____18901 with
        | (head,args) ->
            let uu____18969 =
              let uu____18984 =
                let uu____18985 = un_uinst head  in
                uu____18985.FStar_Syntax_Syntax.n  in
              (uu____18984, args)  in
            (match uu____18969 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____19007,uu____19008)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____19060 ->
                 let uu____19075 =
                   let uu____19081 =
                     let uu____19083 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____19083
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____19081)  in
                 FStar_Errors.raise_error uu____19075
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____19126 =
            let uu____19143 = unmeta t1  in
            FStar_All.pipe_right uu____19143 head_and_args  in
          match uu____19126 with
          | (head,args) ->
              let uu____19190 =
                let uu____19205 =
                  let uu____19206 = un_uinst head  in
                  uu____19206.FStar_Syntax_Syntax.n  in
                (uu____19205, args)  in
              (match uu____19190 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19225)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19262 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19292 = smt_pat_or t1  in
            (match uu____19292 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19314 = list_elements1 e  in
                 FStar_All.pipe_right uu____19314
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19344 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19344
                           (FStar_List.map one_pat)))
             | uu____19373 ->
                 let uu____19378 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19378])
        | uu____19433 ->
            let uu____19436 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19436]
         in
      let uu____19491 =
        let uu____19524 =
          let uu____19525 = FStar_Syntax_Subst.compress t  in
          uu____19525.FStar_Syntax_Syntax.n  in
        match uu____19524 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19582 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19582 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19653;
                        FStar_Syntax_Syntax.effect_name = uu____19654;
                        FStar_Syntax_Syntax.result_typ = uu____19655;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19657)::(post,uu____19659)::(pats,uu____19661)::[];
                        FStar_Syntax_Syntax.flags = uu____19662;_}
                      ->
                      let uu____19723 = lemma_pats pats  in
                      (binders1, pre, post, uu____19723)
                  | uu____19760 -> failwith "impos"))
        | uu____19794 -> failwith "Impos"  in
      match uu____19491 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19886 =
              let uu____19893 =
                let uu____19894 =
                  let uu____19901 = mk_imp pre post1  in
                  let uu____19904 =
                    let uu____19905 =
                      let uu____19926 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19926, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19905  in
                  (uu____19901, uu____19904)  in
                FStar_Syntax_Syntax.Tm_meta uu____19894  in
              FStar_Syntax_Syntax.mk uu____19893  in
            uu____19886 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19950 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19950 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19980 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____19991 -> true
    | uu____19993 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____20004 -> true
    | uu____20006 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____20024 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____20025 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____20026 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____20027 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____20028 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____20029 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____20030 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____20031 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____20034 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____20037 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____20024;
        FStar_Syntax_Syntax.bind_wp = uu____20025;
        FStar_Syntax_Syntax.stronger = uu____20026;
        FStar_Syntax_Syntax.if_then_else = uu____20027;
        FStar_Syntax_Syntax.ite_wp = uu____20028;
        FStar_Syntax_Syntax.close_wp = uu____20029;
        FStar_Syntax_Syntax.trivial = uu____20030;
        FStar_Syntax_Syntax.repr = uu____20031;
        FStar_Syntax_Syntax.return_repr = uu____20034;
        FStar_Syntax_Syntax.bind_repr = uu____20037
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____20069 =
        match uu____20069 with
        | (ts1,ts2) ->
            let uu____20080 = f ts1  in
            let uu____20081 = f ts2  in (uu____20080, uu____20081)
         in
      let uu____20082 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____20087 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____20092 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____20097 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____20102 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____20082;
        FStar_Syntax_Syntax.l_return = uu____20087;
        FStar_Syntax_Syntax.l_bind = uu____20092;
        FStar_Syntax_Syntax.l_subcomp = uu____20097;
        FStar_Syntax_Syntax.l_if_then_else = uu____20102
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
          let uu____20124 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____20124
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____20126 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____20126
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____20128 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____20128
  
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
    | uu____20143 -> FStar_Pervasives_Native.None
  
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
        let uu____20157 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20157
          (fun uu____20164  -> FStar_Pervasives_Native.Some uu____20164)
  
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
        let uu____20204 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20204
          (fun uu____20211  -> FStar_Pervasives_Native.Some uu____20211)
  
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
        let uu____20225 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20225
          (fun uu____20232  -> FStar_Pervasives_Native.Some uu____20232)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20246  -> FStar_Pervasives_Native.Some uu____20246)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20250  -> FStar_Pervasives_Native.Some uu____20250)
    | uu____20251 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20263 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20263
          (fun uu____20270  -> FStar_Pervasives_Native.Some uu____20270)
    | uu____20271 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20285  -> FStar_Pervasives_Native.Some uu____20285)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20289  -> FStar_Pervasives_Native.Some uu____20289)
    | uu____20290 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20304  -> FStar_Pervasives_Native.Some uu____20304)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20308  -> FStar_Pervasives_Native.Some uu____20308)
    | uu____20309 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20333 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20334 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20336 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20336
          (fun uu____20343  -> FStar_Pervasives_Native.Some uu____20343)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun uu____20357  -> FStar_Pervasives_Native.Some uu____20357)
    | uu____20358 -> FStar_Pervasives_Native.None
  