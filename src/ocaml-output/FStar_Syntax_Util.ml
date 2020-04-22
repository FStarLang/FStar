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
          let err1 uu____1666 =
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEffect, err) r
             in
          let repr1 = FStar_Syntax_Subst.compress repr  in
          if is_layered
          then
            match repr1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_app (uu____1676,uu____1677::is) ->
                FStar_All.pipe_right is
                  (FStar_List.map FStar_Pervasives_Native.fst)
            | uu____1745 -> err1 ()
          else
            (match repr1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_arrow (uu____1750,c) ->
                 let uu____1772 = FStar_All.pipe_right c comp_to_comp_typ  in
                 FStar_All.pipe_right uu____1772
                   (fun ct  ->
                      FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                        (FStar_List.map FStar_Pervasives_Native.fst))
             | uu____1807 -> err1 ())
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1828)::[] -> wp
      | uu____1853 ->
          let uu____1864 =
            let uu____1866 =
              FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name  in
            let uu____1868 =
              let uu____1870 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length
                 in
              FStar_All.pipe_right uu____1870 FStar_Util.string_of_int  in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args"
              uu____1866 uu____1868
             in
          failwith uu____1864
       in
    let uu____1894 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1894, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1908 -> true
    | FStar_Syntax_Syntax.GTotal uu____1918 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1943  ->
               match uu___0_1943 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1947 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1964  ->
            match uu___1_1964 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1968 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____2000 -> true
    | FStar_Syntax_Syntax.GTotal uu____2010 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_2025  ->
                   match uu___2_2025 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____2028 -> false)))
  
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
    let uu____2069 =
      let uu____2070 = FStar_Syntax_Subst.compress t  in
      uu____2070.FStar_Syntax_Syntax.n  in
    match uu____2069 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____2074,c) -> is_pure_or_ghost_comp c
    | uu____2096 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____2111 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2120 =
      let uu____2121 = FStar_Syntax_Subst.compress t  in
      uu____2121.FStar_Syntax_Syntax.n  in
    match uu____2120 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____2125,c) -> is_lemma_comp c
    | uu____2147 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2155 =
      let uu____2156 = FStar_Syntax_Subst.compress t  in
      uu____2156.FStar_Syntax_Syntax.n  in
    match uu____2155 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____2160) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____2186) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2223,t1,uu____2225) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2251,uu____2252) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2294) -> head_of t1
    | uu____2299 -> t
  
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
    | uu____2377 -> (t1, [])
  
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
        let uu____2459 = head_and_args' head  in
        (match uu____2459 with
         | (head1,args') -> (head1, (FStar_List.append args' args)))
    | uu____2528 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2555) ->
        FStar_Syntax_Subst.compress t2
    | uu____2560 -> t1
  
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
                (fun uu___3_2578  ->
                   match uu___3_2578 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____2581 -> false)))
    | uu____2583 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2600) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____2610) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2639 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2648 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___393_2660 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___393_2660.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___393_2660.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___393_2660.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___393_2660.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2676  ->
            match uu___4_2676 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____2680 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2688 -> []
    | FStar_Syntax_Syntax.GTotal uu____2705 -> []
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
    | uu____2749 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2759,uu____2760) ->
        unascribe e2
    | uu____2801 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2854,uu____2855) ->
          ascribe t' k
      | uu____2896 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2923 =
      let uu____2932 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2932  in
    uu____2923 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2988 =
      let uu____2989 = FStar_Syntax_Subst.compress t  in
      uu____2989.FStar_Syntax_Syntax.n  in
    match uu____2988 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2993 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2993
    | uu____2994 -> t
  
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3001 =
      let uu____3002 = FStar_Syntax_Subst.compress t  in
      uu____3002.FStar_Syntax_Syntax.n  in
    match uu____3001 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____3006 ->
             let uu____3015 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____3015
         | uu____3016 -> t)
    | uu____3017 -> t
  
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
      | uu____3042 -> false
  
let unlazy_as_t :
  'uuuuuu3055 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'uuuuuu3055
  =
  fun k  ->
    fun t  ->
      let uu____3066 =
        let uu____3067 = FStar_Syntax_Subst.compress t  in
        uu____3067.FStar_Syntax_Syntax.n  in
      match uu____3066 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____3072;
            FStar_Syntax_Syntax.rng = uu____3073;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____3076 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____3117 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____3117;
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
    let uu____3130 =
      let uu____3145 = unascribe t  in head_and_args' uu____3145  in
    match uu____3130 with
    | (hd,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____3179 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____3190 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____3201 -> false
  
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
      | (NotEqual ,uu____3251) -> NotEqual
      | (uu____3252,NotEqual ) -> NotEqual
      | (Unknown ,uu____3253) -> Unknown
      | (uu____3254,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___5_3363 = if uu___5_3363 then Equal else Unknown  in
      let equal_iff uu___6_3374 = if uu___6_3374 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____3395 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____3417 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____3417
        then
          let uu____3421 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____3498  ->
                    match uu____3498 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____3539 = eq_tm a1 a2  in
                        eq_inj acc uu____3539) Equal) uu____3421
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____3553 =
          let uu____3570 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____3570 head_and_args  in
        match uu____3553 with
        | (head1,args1) ->
            let uu____3623 =
              let uu____3640 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____3640 head_and_args  in
            (match uu____3623 with
             | (head2,args2) ->
                 let uu____3693 =
                   let uu____3698 =
                     let uu____3699 = un_uinst head1  in
                     uu____3699.FStar_Syntax_Syntax.n  in
                   let uu____3702 =
                     let uu____3703 = un_uinst head2  in
                     uu____3703.FStar_Syntax_Syntax.n  in
                   (uu____3698, uu____3702)  in
                 (match uu____3693 with
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
                  | uu____3730 -> FStar_Pervasives_Native.None))
         in
      let t12 = unmeta t11  in
      let t22 = unmeta t21  in
      match ((t12.FStar_Syntax_Syntax.n), (t22.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3748,uu____3749) ->
          let uu____3750 = unlazy t12  in eq_tm uu____3750 t22
      | (uu____3751,FStar_Syntax_Syntax.Tm_lazy uu____3752) ->
          let uu____3753 = unlazy t22  in eq_tm t12 uu____3753
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          let uu____3756 = FStar_Syntax_Syntax.bv_eq a b  in
          equal_if uu____3756
      | uu____3758 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3782 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____3782
            (fun uu____3830  ->
               match uu____3830 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3845 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____3845
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____3859 = eq_tm f g  in
          eq_and uu____3859
            (fun uu____3862  ->
               let uu____3863 = eq_univs_list us vs  in equal_if uu____3863)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3865),uu____3866) -> Unknown
      | (uu____3867,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3868)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____3871 = FStar_Const.eq_const c d  in equal_iff uu____3871
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____3874)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____3876))) ->
          let uu____3905 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____3905
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____3959 =
            let uu____3964 =
              let uu____3965 = un_uinst h1  in
              uu____3965.FStar_Syntax_Syntax.n  in
            let uu____3968 =
              let uu____3969 = un_uinst h2  in
              uu____3969.FStar_Syntax_Syntax.n  in
            (uu____3964, uu____3968)  in
          (match uu____3959 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3975 =
                    let uu____3977 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____3977  in
                  FStar_List.mem uu____3975 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3979 ->
               let uu____3984 = eq_tm h1 h2  in
               eq_and uu____3984 (fun uu____3986  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t13,bs1),FStar_Syntax_Syntax.Tm_match
         (t23,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____4092 = FStar_List.zip bs1 bs2  in
            let uu____4155 = eq_tm t13 t23  in
            FStar_List.fold_right
              (fun uu____4192  ->
                 fun a  ->
                   match uu____4192 with
                   | (b1,b2) ->
                       eq_and a (fun uu____4285  -> branch_matches b1 b2))
              uu____4092 uu____4155
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v) ->
          let uu____4290 = eq_univs u v  in equal_if uu____4290
      | (FStar_Syntax_Syntax.Tm_quoted (t13,q1),FStar_Syntax_Syntax.Tm_quoted
         (t23,q2)) ->
          let uu____4304 = eq_quoteinfo q1 q2  in
          eq_and uu____4304 (fun uu____4306  -> eq_tm t13 t23)
      | (FStar_Syntax_Syntax.Tm_refine
         (t13,phi1),FStar_Syntax_Syntax.Tm_refine (t23,phi2)) ->
          let uu____4319 =
            eq_tm t13.FStar_Syntax_Syntax.sort t23.FStar_Syntax_Syntax.sort
             in
          eq_and uu____4319 (fun uu____4321  -> eq_tm phi1 phi2)
      | uu____4322 -> Unknown

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
      | ([],uu____4394) -> NotEqual
      | (uu____4425,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          let uu____4514 =
            let uu____4516 = FStar_Syntax_Syntax.bv_eq x1 x2  in
            Prims.op_Negation uu____4516  in
          if uu____4514
          then NotEqual
          else
            (let uu____4521 = eq_tm t1 t2  in
             match uu____4521 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____4522 = eq_antiquotes a11 a21  in
                 (match uu____4522 with
                  | NotEqual  -> NotEqual
                  | uu____4523 -> Unknown)
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
        | (uu____4607,uu____4608) -> false  in
      let uu____4618 = b1  in
      match uu____4618 with
      | (p1,w1,t1) ->
          let uu____4652 = b2  in
          (match uu____4652 with
           | (p2,w2,t2) ->
               let uu____4686 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____4686
               then
                 let uu____4689 =
                   (let uu____4693 = eq_tm t1 t2  in uu____4693 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____4702 = eq_tm t11 t21  in
                             uu____4702 = Equal) w1 w2)
                    in
                 (if uu____4689 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____4767)::a11,(b,uu____4770)::b1) ->
          let uu____4844 = eq_tm a b  in
          (match uu____4844 with
           | Equal  -> eq_args a11 b1
           | uu____4845 -> Unknown)
      | uu____4846 -> Unknown

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
      | (FStar_Pervasives_Native.None ,uu____4901) -> NotEqual
      | (uu____4908,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____4938 -> NotEqual
  
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____4955) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4961,uu____4962) ->
        unrefine t2
    | uu____5003 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5011 =
      let uu____5012 = FStar_Syntax_Subst.compress t  in
      uu____5012.FStar_Syntax_Syntax.n  in
    match uu____5011 with
    | FStar_Syntax_Syntax.Tm_uvar uu____5016 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5031) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____5036 ->
        let uu____5053 =
          let uu____5054 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____5054 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____5053 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____5117,uu____5118) ->
        is_uvar t1
    | uu____5159 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5168 =
      let uu____5169 = unrefine t  in uu____5169.FStar_Syntax_Syntax.n  in
    match uu____5168 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head,uu____5175) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5201) -> is_unit t1
    | uu____5206 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5215 =
      let uu____5216 = FStar_Syntax_Subst.compress t  in
      uu____5216.FStar_Syntax_Syntax.n  in
    match uu____5215 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5221 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____5230 =
      let uu____5231 = FStar_Syntax_Subst.compress e  in
      uu____5231.FStar_Syntax_Syntax.n  in
    match uu____5230 with
    | FStar_Syntax_Syntax.Tm_abs uu____5235 -> true
    | uu____5255 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5264 =
      let uu____5265 = FStar_Syntax_Subst.compress t  in
      uu____5265.FStar_Syntax_Syntax.n  in
    match uu____5264 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5269 -> true
    | uu____5285 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____5295) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5301,uu____5302) ->
        pre_typ t2
    | uu____5343 -> t1
  
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
      let uu____5368 =
        let uu____5369 = un_uinst typ1  in uu____5369.FStar_Syntax_Syntax.n
         in
      match uu____5368 with
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let head1 = un_uinst head  in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5434 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5464 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5485,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____5492) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5497,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____5508,uu____5509,uu____5510,uu____5511,uu____5512) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____5522,uu____5523,uu____5524,uu____5525) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____5531,uu____5532,uu____5533,uu____5534,uu____5535) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____5543,uu____5544) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____5546,uu____5547) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5549 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5550 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5551 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5564 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____5575 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5597 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5623  ->
    match uu___7_5623 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'uuuuuu5637 'uuuuuu5638 .
    ('uuuuuu5637 FStar_Syntax_Syntax.syntax * 'uuuuuu5638) ->
      FStar_Range.range
  =
  fun uu____5649  ->
    match uu____5649 with | (hd,uu____5657) -> hd.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'uuuuuu5671 'uuuuuu5672 .
    ('uuuuuu5671 FStar_Syntax_Syntax.syntax * 'uuuuuu5672) Prims.list ->
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
      | uu____5770 ->
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
      let uu____5829 =
        FStar_List.map
          (fun uu____5856  ->
             match uu____5856 with
             | (bv,aq) ->
                 let uu____5875 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____5875, aq)) bs
         in
      mk_app f uu____5829
  
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
          (let uu____5926 =
             let uu____5932 =
               let uu____5934 =
                 let uu____5936 = FStar_Ident.ident_of_lid lid  in
                 FStar_Ident.text_of_id uu____5936  in
               mk_field_projector_name_from_string uu____5934 itext  in
             let uu____5937 = FStar_Ident.range_of_id i  in
             (uu____5932, uu____5937)  in
           FStar_Ident.mk_ident uu____5926)
         in
      let uu____5939 =
        let uu____5940 = FStar_Ident.ns_of_lid lid  in
        FStar_List.append uu____5940 [newi]  in
      FStar_Ident.lid_of_ids uu____5939
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____5962 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____5962
          then
            let uu____5965 =
              let uu____5971 =
                let uu____5973 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____5973  in
              let uu____5976 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____5971, uu____5976)  in
            FStar_Ident.mk_ident uu____5965
          else x.FStar_Syntax_Syntax.ppname  in
        mk_field_projector_name_from_ident lid nm
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5991) -> ses
    | uu____6000 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____6015 = FStar_Syntax_Unionfind.find uv  in
      match uu____6015 with
      | FStar_Pervasives_Native.Some uu____6018 ->
          let uu____6019 =
            let uu____6021 =
              let uu____6023 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____6023  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____6021  in
          failwith uu____6019
      | uu____6028 -> FStar_Syntax_Unionfind.change uv t
  
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
            (let uu____6052 = FStar_Ident.text_of_id l1b  in
             let uu____6054 = FStar_Ident.text_of_id l2b  in
             uu____6052 = uu____6054)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____6083 = FStar_Ident.text_of_id x1  in
                      let uu____6085 = FStar_Ident.text_of_id x2  in
                      uu____6083 = uu____6085) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____6094 = FStar_Ident.text_of_id x1  in
                    let uu____6096 = FStar_Ident.text_of_id x2  in
                    uu____6094 = uu____6096) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  ->
                      let uu____6125 = FStar_Ident.text_of_id x1  in
                      let uu____6127 = FStar_Ident.text_of_id x2  in
                      uu____6125 = uu____6127) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  ->
                    let uu____6136 = FStar_Ident.text_of_id x1  in
                    let uu____6138 = FStar_Ident.text_of_id x2  in
                    uu____6136 = uu____6138) f1 f2)
      | uu____6141 -> q1 = q2
  
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
              let uu____6187 =
                let uu___1023_6188 = rc  in
                let uu____6189 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1023_6188.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6189;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1023_6188.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____6187
           in
        match bs with
        | [] -> t
        | uu____6206 ->
            let body =
              let uu____6208 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____6208  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____6238 =
                   let uu____6245 =
                     let uu____6246 =
                       let uu____6265 =
                         let uu____6274 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____6274 bs'  in
                       let uu____6289 = close_lopt lopt'  in
                       (uu____6265, t1, uu____6289)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6246  in
                   FStar_Syntax_Syntax.mk uu____6245  in
                 uu____6238 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____6304 ->
                 let uu____6305 =
                   let uu____6312 =
                     let uu____6313 =
                       let uu____6332 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____6341 = close_lopt lopt  in
                       (uu____6332, body, uu____6341)  in
                     FStar_Syntax_Syntax.Tm_abs uu____6313  in
                   FStar_Syntax_Syntax.mk uu____6312  in
                 uu____6305 FStar_Pervasives_Native.None
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
      | uu____6397 ->
          let uu____6406 =
            let uu____6413 =
              let uu____6414 =
                let uu____6429 = FStar_Syntax_Subst.close_binders bs  in
                let uu____6438 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____6429, uu____6438)  in
              FStar_Syntax_Syntax.Tm_arrow uu____6414  in
            FStar_Syntax_Syntax.mk uu____6413  in
          uu____6406 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____6487 =
        let uu____6488 = FStar_Syntax_Subst.compress t  in
        uu____6488.FStar_Syntax_Syntax.n  in
      match uu____6487 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____6518) ->
               let uu____6527 =
                 let uu____6528 = FStar_Syntax_Subst.compress tres  in
                 uu____6528.FStar_Syntax_Syntax.n  in
               (match uu____6527 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____6571 -> t)
           | uu____6572 -> t)
      | uu____6573 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____6591 =
        let uu____6592 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____6592 t.FStar_Syntax_Syntax.pos  in
      let uu____6593 =
        let uu____6600 =
          let uu____6601 =
            let uu____6608 =
              let uu____6611 =
                let uu____6612 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____6612]  in
              FStar_Syntax_Subst.close uu____6611 t  in
            (b, uu____6608)  in
          FStar_Syntax_Syntax.Tm_refine uu____6601  in
        FStar_Syntax_Syntax.mk uu____6600  in
      uu____6593 FStar_Pervasives_Native.None uu____6591
  
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
        let uu____6692 = is_total_comp c  in
        if uu____6692
        then
          let uu____6707 = arrow_formals_comp_ln (comp_result c)  in
          (match uu____6707 with
           | (bs',k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6774;
           FStar_Syntax_Syntax.index = uu____6775;
           FStar_Syntax_Syntax.sort = s;_},uu____6777)
        ->
        let rec aux s1 k2 =
          let uu____6808 =
            let uu____6809 = FStar_Syntax_Subst.compress s1  in
            uu____6809.FStar_Syntax_Syntax.n  in
          match uu____6808 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6824 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6839;
                 FStar_Syntax_Syntax.index = uu____6840;
                 FStar_Syntax_Syntax.sort = s2;_},uu____6842)
              -> aux s2 k2
          | uu____6850 ->
              let uu____6851 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____6851)
           in
        aux s k1
    | uu____6866 ->
        let uu____6867 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____6867)
  
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let uu____6892 = arrow_formals_comp_ln k  in
    match uu____6892 with | (bs,c) -> FStar_Syntax_Subst.open_comp bs c
  
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____6947 = arrow_formals_comp_ln k  in
    match uu____6947 with | (bs,c) -> (bs, (comp_result c))
  
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____7014 = arrow_formals_comp k  in
    match uu____7014 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7116 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7116 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____7140 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___8_7149  ->
                         match uu___8_7149 with
                         | FStar_Syntax_Syntax.DECREASES uu____7151 -> true
                         | uu____7155 -> false))
                  in
               (match uu____7140 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7190 ->
                    let uu____7193 = is_total_comp c1  in
                    if uu____7193
                    then
                      let uu____7212 = arrow_until_decreases (comp_result c1)
                         in
                      (match uu____7212 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7305;
             FStar_Syntax_Syntax.index = uu____7306;
             FStar_Syntax_Syntax.sort = k2;_},uu____7308)
          -> arrow_until_decreases k2
      | uu____7316 -> ([], FStar_Pervasives_Native.None)  in
    let uu____7337 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____7337 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____7391 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____7412 =
                 FStar_Common.tabulate n_univs (fun uu____7418  -> false)  in
               let uu____7421 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7446  ->
                         match uu____7446 with
                         | (x,uu____7455) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____7412 uu____7421)
           in
        ((n_univs + (FStar_List.length bs)), uu____7391)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7511 =
            let uu___1150_7512 = rc  in
            let uu____7513 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1150_7512.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7513;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1150_7512.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____7511
      | uu____7522 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____7556 =
        let uu____7557 =
          let uu____7560 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____7560  in
        uu____7557.FStar_Syntax_Syntax.n  in
      match uu____7556 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____7606 = aux t2 what  in
          (match uu____7606 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7678 -> ([], t1, abs_body_lcomp)  in
    let uu____7695 = aux t FStar_Pervasives_Native.None  in
    match uu____7695 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____7743 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____7743 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let no_acc uu____7777 =
      match uu____7777 with
      | (b,aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true )) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7791 -> aq  in
          (b, aq1)
       in
    let uu____7796 = arrow_formals_comp_ln t  in
    match uu____7796 with
    | (bs,c) ->
        (match bs with
         | [] -> t
         | uu____7833 ->
             let uu____7842 =
               let uu____7849 =
                 let uu____7850 =
                   let uu____7865 = FStar_List.map no_acc bs  in
                   (uu____7865, c)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____7850  in
               FStar_Syntax_Syntax.mk uu____7849  in
             uu____7842 FStar_Pervasives_Native.None
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
                    | (FStar_Pervasives_Native.None ,uu____8036) -> def
                    | (uu____8047,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____8059) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu____8075  ->
                                  FStar_Syntax_Syntax.U_name uu____8075))
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
            let uu____8157 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____8157 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____8192 ->
            let t' = arrow binders c  in
            let uu____8204 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____8204 with
             | (uvs1,t'1) ->
                 let uu____8225 =
                   let uu____8226 = FStar_Syntax_Subst.compress t'1  in
                   uu____8226.FStar_Syntax_Syntax.n  in
                 (match uu____8225 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____8275 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8300 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        FStar_Parser_Const.is_tuple_constructor_string uu____8300
    | uu____8302 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8313 -> false
  
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
      let uu____8376 =
        let uu____8377 = pre_typ t  in uu____8377.FStar_Syntax_Syntax.n  in
      match uu____8376 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8382 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____8396 =
        let uu____8397 = pre_typ t  in uu____8397.FStar_Syntax_Syntax.n  in
      match uu____8396 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8401 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____8403) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8429) ->
          is_constructed_typ t1 lid
      | uu____8434 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8447 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8448 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8449 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8451) -> get_tycon t2
    | uu____8476 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8484 =
      let uu____8485 = un_uinst t  in uu____8485.FStar_Syntax_Syntax.n  in
    match uu____8484 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8490 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8504 =
        let uu____8508 = FStar_List.splitAt (Prims.of_int (2)) path  in
        FStar_Pervasives_Native.fst uu____8508  in
      match uu____8504 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8540 -> false
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
  fun uu____8559  ->
    let u =
      let uu____8565 =
        FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
      FStar_All.pipe_left
        (fun uu____8586  -> FStar_Syntax_Syntax.U_unif uu____8586) uu____8565
       in
    let uu____8587 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____8587, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____8600 = eq_tm a a'  in
      match uu____8600 with | Equal  -> true | uu____8603 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8608 =
    let uu____8615 =
      let uu____8616 =
        let uu____8617 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____8617
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____8616  in
    FStar_Syntax_Syntax.mk uu____8615  in
  uu____8608 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____8730 =
            let uu____8733 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____8734 =
              let uu____8741 =
                let uu____8742 =
                  let uu____8759 =
                    let uu____8770 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____8779 =
                      let uu____8790 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____8790]  in
                    uu____8770 :: uu____8779  in
                  (tand, uu____8759)  in
                FStar_Syntax_Syntax.Tm_app uu____8742  in
              FStar_Syntax_Syntax.mk uu____8741  in
            uu____8734 FStar_Pervasives_Native.None uu____8733  in
          FStar_Pervasives_Native.Some uu____8730
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____8867 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____8868 =
          let uu____8875 =
            let uu____8876 =
              let uu____8893 =
                let uu____8904 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____8913 =
                  let uu____8924 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____8924]  in
                uu____8904 :: uu____8913  in
              (op_t, uu____8893)  in
            FStar_Syntax_Syntax.Tm_app uu____8876  in
          FStar_Syntax_Syntax.mk uu____8875  in
        uu____8868 FStar_Pervasives_Native.None uu____8867
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____8981 =
      let uu____8988 =
        let uu____8989 =
          let uu____9006 =
            let uu____9017 = FStar_Syntax_Syntax.as_arg phi  in [uu____9017]
             in
          (t_not, uu____9006)  in
        FStar_Syntax_Syntax.Tm_app uu____8989  in
      FStar_Syntax_Syntax.mk uu____8988  in
    uu____8981 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____9214 =
      let uu____9221 =
        let uu____9222 =
          let uu____9239 =
            let uu____9250 = FStar_Syntax_Syntax.as_arg e  in [uu____9250]
             in
          (b2t_v, uu____9239)  in
        FStar_Syntax_Syntax.Tm_app uu____9222  in
      FStar_Syntax_Syntax.mk uu____9221  in
    uu____9214 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9297 = head_and_args e  in
    match uu____9297 with
    | (hd,args) ->
        let uu____9342 =
          let uu____9357 =
            let uu____9358 = FStar_Syntax_Subst.compress hd  in
            uu____9358.FStar_Syntax_Syntax.n  in
          (uu____9357, args)  in
        (match uu____9342 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____9375)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9410 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9432 =
      let uu____9433 = unmeta t  in uu____9433.FStar_Syntax_Syntax.n  in
    match uu____9432 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9438 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9461 = is_t_true t1  in
      if uu____9461
      then t2
      else
        (let uu____9468 = is_t_true t2  in
         if uu____9468 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____9496 = is_t_true t1  in
      if uu____9496
      then t_true
      else
        (let uu____9503 = is_t_true t2  in
         if uu____9503 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____9532 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____9533 =
        let uu____9540 =
          let uu____9541 =
            let uu____9558 =
              let uu____9569 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____9578 =
                let uu____9589 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____9589]  in
              uu____9569 :: uu____9578  in
            (teq, uu____9558)  in
          FStar_Syntax_Syntax.Tm_app uu____9541  in
        FStar_Syntax_Syntax.mk uu____9540  in
      uu____9533 FStar_Pervasives_Native.None uu____9532
  
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
          let uu____9656 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____9657 =
            let uu____9664 =
              let uu____9665 =
                let uu____9682 =
                  let uu____9693 = FStar_Syntax_Syntax.iarg t  in
                  let uu____9702 =
                    let uu____9713 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____9722 =
                      let uu____9733 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____9733]  in
                    uu____9713 :: uu____9722  in
                  uu____9693 :: uu____9702  in
                (eq_inst, uu____9682)  in
              FStar_Syntax_Syntax.Tm_app uu____9665  in
            FStar_Syntax_Syntax.mk uu____9664  in
          uu____9657 FStar_Pervasives_Native.None uu____9656
  
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
        let uu____9810 =
          let uu____9817 =
            let uu____9818 =
              let uu____9835 =
                let uu____9846 = FStar_Syntax_Syntax.iarg t  in
                let uu____9855 =
                  let uu____9866 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____9875 =
                    let uu____9886 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____9886]  in
                  uu____9866 :: uu____9875  in
                uu____9846 :: uu____9855  in
              (t_has_type1, uu____9835)  in
            FStar_Syntax_Syntax.Tm_app uu____9818  in
          FStar_Syntax_Syntax.mk uu____9817  in
        uu____9810 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____9963 =
          let uu____9970 =
            let uu____9971 =
              let uu____9988 =
                let uu____9999 = FStar_Syntax_Syntax.iarg t  in
                let uu____10008 =
                  let uu____10019 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____10019]  in
                uu____9999 :: uu____10008  in
              (t_with_type1, uu____9988)  in
            FStar_Syntax_Syntax.Tm_app uu____9971  in
          FStar_Syntax_Syntax.mk uu____9970  in
        uu____9963 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____10066 =
    let uu____10073 =
      let uu____10074 =
        let uu____10081 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____10081, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____10074  in
    FStar_Syntax_Syntax.mk uu____10073  in
  uu____10066 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
        let uu____10164 =
          let uu____10171 =
            let uu____10172 =
              let uu____10189 =
                let uu____10200 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____10209 =
                  let uu____10220 =
                    let uu____10229 =
                      let uu____10230 =
                        let uu____10231 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____10231]  in
                      abs uu____10230 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____10229  in
                  [uu____10220]  in
                uu____10200 :: uu____10209  in
              (fa, uu____10189)  in
            FStar_Syntax_Syntax.Tm_app uu____10172  in
          FStar_Syntax_Syntax.mk uu____10171  in
        uu____10164 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____10358 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____10358
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10377 -> true
    | uu____10379 -> false
  
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
          let uu____10426 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____10426, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____10455 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____10455, FStar_Pervasives_Native.None, t2)  in
        let uu____10469 =
          let uu____10470 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10470  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____10469
  
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
      let uu____10546 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10549 =
        let uu____10560 = FStar_Syntax_Syntax.as_arg p  in [uu____10560]  in
      mk_app uu____10546 uu____10549
  
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
      let uu____10600 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____10603 =
        let uu____10614 = FStar_Syntax_Syntax.as_arg p  in [uu____10614]  in
      mk_app uu____10600 uu____10603
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10649 = head_and_args t  in
    match uu____10649 with
    | (head,args) ->
        let head1 = unascribe head  in
        let head2 = un_uinst head1  in
        let uu____10698 =
          let uu____10713 =
            let uu____10714 = FStar_Syntax_Subst.compress head2  in
            uu____10714.FStar_Syntax_Syntax.n  in
          (uu____10713, args)  in
        (match uu____10698 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____10733)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10799 =
                    let uu____10804 =
                      let uu____10805 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____10805]  in
                    FStar_Syntax_Subst.open_term uu____10804 p  in
                  (match uu____10799 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10862 -> failwith "impossible"  in
                       let uu____10870 =
                         let uu____10872 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10872
                          in
                       if uu____10870
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10888 -> FStar_Pervasives_Native.None)
         | uu____10891 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____10922 = head_and_args t  in
    match uu____10922 with
    | (head,args) ->
        let uu____10973 =
          let uu____10988 =
            let uu____10989 = FStar_Syntax_Subst.compress head  in
            uu____10989.FStar_Syntax_Syntax.n  in
          (uu____10988, args)  in
        (match uu____10973 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____11011;
               FStar_Syntax_Syntax.vars = uu____11012;_},u::[]),(t1,uu____11015)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11062 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11097 = head_and_args t  in
    match uu____11097 with
    | (head,args) ->
        let uu____11148 =
          let uu____11163 =
            let uu____11164 = FStar_Syntax_Subst.compress head  in
            uu____11164.FStar_Syntax_Syntax.n  in
          (uu____11163, args)  in
        (match uu____11148 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____11186;
               FStar_Syntax_Syntax.vars = uu____11187;_},u::[]),(t1,uu____11190)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11237 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11265 =
      let uu____11282 = unmeta t  in head_and_args uu____11282  in
    match uu____11265 with
    | (head,uu____11285) ->
        let uu____11310 =
          let uu____11311 = un_uinst head  in
          uu____11311.FStar_Syntax_Syntax.n  in
        (match uu____11310 with
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
         | uu____11316 -> false)
  
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11336 =
      let uu____11337 = FStar_Syntax_Subst.compress t  in
      uu____11337.FStar_Syntax_Syntax.n  in
    match uu____11336 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____11443 =
          let uu____11448 =
            let uu____11449 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____11449  in
          (b, uu____11448)  in
        FStar_Pervasives_Native.Some uu____11443
    | uu____11454 -> FStar_Pervasives_Native.None
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____11477 = arrow_one_ln t  in
    FStar_Util.bind_opt uu____11477
      (fun uu____11505  ->
         match uu____11505 with
         | (b,c) ->
             let uu____11524 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____11524 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11587 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____11624 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____11624
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____11676 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____11719 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____11760 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____12146) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____12158) ->
          unmeta_monadic t
      | uu____12171 -> f2  in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args  in
      let aux uu____12240 =
        match uu____12240 with
        | (arity,lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12278  ->
                   match uu____12278 with
                   | (lid,out_lid) ->
                       let uu____12287 =
                         FStar_Ident.lid_equals target_lid lid  in
                       if uu____12287
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None
         in
      FStar_Util.find_map table aux  in
    let destruct_base_conn t =
      let uu____12314 = head_and_args t  in
      match uu____12314 with
      | (hd,args) ->
          let uu____12359 =
            let uu____12360 = un_uinst hd  in
            uu____12360.FStar_Syntax_Syntax.n  in
          (match uu____12359 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12366 -> FStar_Pervasives_Native.None)
       in
    let destruct_sq_base_conn t =
      let uu____12375 = un_squash t  in
      FStar_Util.bind_opt uu____12375
        (fun t1  ->
           let uu____12391 = head_and_args' t1  in
           match uu____12391 with
           | (hd,args) ->
               let uu____12430 =
                 let uu____12431 = un_uinst hd  in
                 uu____12431.FStar_Syntax_Syntax.n  in
               (match uu____12430 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12437 -> FStar_Pervasives_Native.None))
       in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____12478,pats)) ->
          let uu____12516 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____12516)
      | uu____12529 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____12596 = head_and_args t1  in
        match uu____12596 with
        | (t2,args) ->
            let uu____12651 = un_uinst t2  in
            let uu____12652 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12693  ->
                      match uu____12693 with
                      | (t3,imp) ->
                          let uu____12712 = unascribe t3  in
                          (uu____12712, imp)))
               in
            (uu____12651, uu____12652)
         in
      let rec aux qopt out t1 =
        let uu____12763 = let uu____12787 = flat t1  in (qopt, uu____12787)
           in
        match uu____12763 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12827;
                 FStar_Syntax_Syntax.vars = uu____12828;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____12831);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____12832;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____12833;_},uu____12834)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____12936;
                 FStar_Syntax_Syntax.vars = uu____12937;_},uu____12938::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____12941);
                  FStar_Syntax_Syntax.pos = uu____12942;
                  FStar_Syntax_Syntax.vars = uu____12943;_},uu____12944)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13061;
               FStar_Syntax_Syntax.vars = uu____13062;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____13065);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____13066;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____13067;_},uu____13068)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13161 =
              let uu____13165 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13165  in
            aux uu____13161 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____13175;
               FStar_Syntax_Syntax.vars = uu____13176;_},uu____13177::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____13180);
                FStar_Syntax_Syntax.pos = uu____13181;
                FStar_Syntax_Syntax.vars = uu____13182;_},uu____13183)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13292 =
              let uu____13296 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____13296  in
            aux uu____13292 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____13306) ->
            let bs = FStar_List.rev out  in
            let uu____13359 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____13359 with
             | (bs1,t2) ->
                 let uu____13368 = patterns t2  in
                 (match uu____13368 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13418 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let rec destruct_sq_forall t =
      let uu____13473 = un_squash t  in
      FStar_Util.bind_opt uu____13473
        (fun t1  ->
           let uu____13488 = arrow_one t1  in
           match uu____13488 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____13503 =
                 let uu____13505 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____13505  in
               if uu____13503
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13515 = comp_to_comp_typ_nouniv c  in
                    uu____13515.FStar_Syntax_Syntax.result_typ  in
                  let uu____13516 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____13516
                  then
                    let uu____13523 = patterns q  in
                    match uu____13523 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13586 =
                       let uu____13587 =
                         let uu____13592 =
                           let uu____13593 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____13604 =
                             let uu____13615 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____13615]  in
                           uu____13593 :: uu____13604  in
                         (FStar_Parser_Const.imp_lid, uu____13592)  in
                       BaseConn uu____13587  in
                     FStar_Pervasives_Native.Some uu____13586))
           | uu____13648 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____13656 = un_squash t  in
      FStar_Util.bind_opt uu____13656
        (fun t1  ->
           let uu____13687 = head_and_args' t1  in
           match uu____13687 with
           | (hd,args) ->
               let uu____13726 =
                 let uu____13741 =
                   let uu____13742 = un_uinst hd  in
                   uu____13742.FStar_Syntax_Syntax.n  in
                 (uu____13741, args)  in
               (match uu____13726 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____13759)::(a2,uu____13761)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13812 =
                      let uu____13813 = FStar_Syntax_Subst.compress a2  in
                      uu____13813.FStar_Syntax_Syntax.n  in
                    (match uu____13812 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____13820) ->
                         let uu____13855 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____13855 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13908 -> failwith "impossible"  in
                              let uu____13916 = patterns q1  in
                              (match uu____13916 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13977 -> FStar_Pervasives_Native.None)
                | uu____13978 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____14001 = destruct_sq_forall phi  in
          (match uu____14001 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____14011  ->
                    FStar_Pervasives_Native.Some uu____14011)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____14018 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____14024 = destruct_sq_exists phi  in
          (match uu____14024 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun uu____14034  ->
                    FStar_Pervasives_Native.Some uu____14034)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____14041 -> f1)
      | uu____14044 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____14048 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____14048
      (fun uu____14053  ->
         let uu____14054 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____14054
           (fun uu____14059  ->
              let uu____14060 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____14060
                (fun uu____14065  ->
                   let uu____14066 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____14066
                     (fun uu____14071  ->
                        let uu____14072 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____14072
                          (fun uu____14076  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____14094 =
            let uu____14099 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____14099  in
          let uu____14100 =
            let uu____14101 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____14101  in
          let uu____14104 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____14094 a.FStar_Syntax_Syntax.action_univs uu____14100
            FStar_Parser_Const.effect_Tot_lid uu____14104 [] pos
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
    let uu____14130 =
      let uu____14137 =
        let uu____14138 =
          let uu____14155 =
            let uu____14166 = FStar_Syntax_Syntax.as_arg t  in [uu____14166]
             in
          (reify_, uu____14155)  in
        FStar_Syntax_Syntax.Tm_app uu____14138  in
      FStar_Syntax_Syntax.mk uu____14137  in
    uu____14130 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____14218 =
        let uu____14225 =
          let uu____14226 =
            let uu____14227 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____14227  in
          FStar_Syntax_Syntax.Tm_constant uu____14226  in
        FStar_Syntax_Syntax.mk uu____14225  in
      uu____14218 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____14229 =
      let uu____14236 =
        let uu____14237 =
          let uu____14254 =
            let uu____14265 = FStar_Syntax_Syntax.as_arg t  in [uu____14265]
             in
          (reflect_, uu____14254)  in
        FStar_Syntax_Syntax.Tm_app uu____14237  in
      FStar_Syntax_Syntax.mk uu____14236  in
    uu____14229 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14309 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14326 = unfold_lazy i  in delta_qualifier uu____14326
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14328 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14329 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14330 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14353 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14366 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14367 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14374 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14375 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14391) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14396;
           FStar_Syntax_Syntax.index = uu____14397;
           FStar_Syntax_Syntax.sort = t2;_},uu____14399)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____14408) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14414,uu____14415) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____14457) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14482,t2,uu____14484) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14509,t2) -> delta_qualifier t2
  
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
    let uu____14548 = delta_qualifier t  in incr_delta_depth uu____14548
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____14556 =
      let uu____14557 = FStar_Syntax_Subst.compress t  in
      uu____14557.FStar_Syntax_Syntax.n  in
    match uu____14556 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____14562 -> false
  
let rec apply_last :
  'uuuuuu14571 .
    ('uuuuuu14571 -> 'uuuuuu14571) ->
      'uuuuuu14571 Prims.list -> 'uuuuuu14571 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14597 = f a  in [uu____14597]
      | x::xs -> let uu____14602 = apply_last f xs  in x :: uu____14602
  
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
          let uu____14657 =
            let uu____14664 =
              let uu____14665 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____14665  in
            FStar_Syntax_Syntax.mk uu____14664  in
          uu____14657 FStar_Pervasives_Native.None rng  in
        let cons args pos =
          let uu____14679 =
            let uu____14684 =
              let uu____14685 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14685
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14684 args  in
          uu____14679 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____14699 =
            let uu____14704 =
              let uu____14705 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____14705
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____14704 args  in
          uu____14699 FStar_Pervasives_Native.None pos  in
        let uu____14706 =
          let uu____14707 =
            let uu____14708 = FStar_Syntax_Syntax.iarg typ  in [uu____14708]
             in
          nil uu____14707 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____14742 =
                 let uu____14743 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____14752 =
                   let uu____14763 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____14772 =
                     let uu____14783 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____14783]  in
                   uu____14763 :: uu____14772  in
                 uu____14743 :: uu____14752  in
               cons uu____14742 t.FStar_Syntax_Syntax.pos) l uu____14706
  
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
        | uu____14892 -> false
  
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
          | uu____15006 -> false
  
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
        | uu____15172 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____15210 = FStar_ST.op_Bang debug_term_eq  in
          if uu____15210
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
        let t11 = let uu____15414 = unmeta_safe t1  in canon_app uu____15414
           in
        let t21 = let uu____15420 = unmeta_safe t2  in canon_app uu____15420
           in
        let uu____15423 =
          let uu____15428 =
            let uu____15429 =
              let uu____15432 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____15432  in
            uu____15429.FStar_Syntax_Syntax.n  in
          let uu____15433 =
            let uu____15434 =
              let uu____15437 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____15437  in
            uu____15434.FStar_Syntax_Syntax.n  in
          (uu____15428, uu____15433)  in
        match uu____15423 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15439,uu____15440) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15449,FStar_Syntax_Syntax.Tm_uinst uu____15450) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15459,uu____15460) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15477,FStar_Syntax_Syntax.Tm_delayed uu____15478) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15495,uu____15496) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15525,FStar_Syntax_Syntax.Tm_ascribed uu____15526) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15565 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____15565
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____15570 = FStar_Const.eq_const c1 c2  in
            check "const" uu____15570
        | (FStar_Syntax_Syntax.Tm_type
           uu____15573,FStar_Syntax_Syntax.Tm_type uu____15574) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____15632 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____15632) &&
              (let uu____15642 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____15642)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____15691 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____15691) &&
              (let uu____15701 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____15701)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (let uu____15718 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort
                in
             check "refine bv sort" uu____15718) &&
              (let uu____15722 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____15722)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____15779 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____15779) &&
              (let uu____15783 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____15783)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____15872 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____15872) &&
              (let uu____15876 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____15876)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15893,uu____15894) ->
            let uu____15895 =
              let uu____15897 = unlazy t11  in
              term_eq_dbg dbg uu____15897 t21  in
            check "lazy_l" uu____15895
        | (uu____15899,FStar_Syntax_Syntax.Tm_lazy uu____15900) ->
            let uu____15901 =
              let uu____15903 = unlazy t21  in
              term_eq_dbg dbg t11 uu____15903  in
            check "lazy_r" uu____15901
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15948 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____15948))
              &&
              (let uu____15952 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____15952)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____15956),FStar_Syntax_Syntax.Tm_uvar (u2,uu____15958)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____16018 =
               let uu____16020 = eq_quoteinfo qi1 qi2  in uu____16020 = Equal
                in
             check "tm_quoted qi" uu____16018) &&
              (let uu____16023 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____16023)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____16053 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____16053) &&
                   (let uu____16057 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____16057)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____16076 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____16076) &&
                    (let uu____16080 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____16080))
                   &&
                   (let uu____16084 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____16084)
             | uu____16087 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____16093) -> fail "unk"
        | (uu____16095,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____16097,uu____16098) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____16100,uu____16101) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____16103,uu____16104) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____16106,uu____16107) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____16109,uu____16110) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____16112,uu____16113) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____16133,uu____16134) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____16150,uu____16151) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____16159,uu____16160) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____16178,uu____16179) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16203,uu____16204) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16219,uu____16220) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16234,uu____16235) ->
            fail "bottom"
        | (uu____16243,FStar_Syntax_Syntax.Tm_bvar uu____16244) ->
            fail "bottom"
        | (uu____16246,FStar_Syntax_Syntax.Tm_name uu____16247) ->
            fail "bottom"
        | (uu____16249,FStar_Syntax_Syntax.Tm_fvar uu____16250) ->
            fail "bottom"
        | (uu____16252,FStar_Syntax_Syntax.Tm_constant uu____16253) ->
            fail "bottom"
        | (uu____16255,FStar_Syntax_Syntax.Tm_type uu____16256) ->
            fail "bottom"
        | (uu____16258,FStar_Syntax_Syntax.Tm_abs uu____16259) ->
            fail "bottom"
        | (uu____16279,FStar_Syntax_Syntax.Tm_arrow uu____16280) ->
            fail "bottom"
        | (uu____16296,FStar_Syntax_Syntax.Tm_refine uu____16297) ->
            fail "bottom"
        | (uu____16305,FStar_Syntax_Syntax.Tm_app uu____16306) ->
            fail "bottom"
        | (uu____16324,FStar_Syntax_Syntax.Tm_match uu____16325) ->
            fail "bottom"
        | (uu____16349,FStar_Syntax_Syntax.Tm_let uu____16350) ->
            fail "bottom"
        | (uu____16365,FStar_Syntax_Syntax.Tm_uvar uu____16366) ->
            fail "bottom"
        | (uu____16380,FStar_Syntax_Syntax.Tm_meta uu____16381) ->
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
               let uu____16416 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____16416)
          (fun q1  ->
             fun q2  ->
               let uu____16428 =
                 let uu____16430 = eq_aqual q1 q2  in uu____16430 = Equal  in
               check "arg qual" uu____16428) a1 a2

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
               let uu____16455 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____16455)
          (fun q1  ->
             fun q2  ->
               let uu____16467 =
                 let uu____16469 = eq_aqual q1 q2  in uu____16469 = Equal  in
               check "binder qual" uu____16467) b1 b2

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
        ((let uu____16483 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____16483) &&
           (let uu____16487 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____16487))
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
    fun uu____16497  ->
      fun uu____16498  ->
        match (uu____16497, uu____16498) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____16625 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____16625) &&
               (let uu____16629 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____16629))
              &&
              (let uu____16633 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____16675 -> false  in
               check "branch when" uu____16633)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____16696 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____16696) &&
           (let uu____16705 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____16705))
          &&
          (let uu____16709 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____16709)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____16726 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____16726 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____16780 ->
        let uu____16795 =
          let uu____16797 = FStar_Syntax_Subst.compress t  in
          sizeof uu____16797  in
        Prims.int_one + uu____16795
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____16800 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16800
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____16804 = sizeof bv.FStar_Syntax_Syntax.sort  in
        Prims.int_one + uu____16804
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____16813 = sizeof t1  in (FStar_List.length us) + uu____16813
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____16817) ->
        let uu____16842 = sizeof t1  in
        let uu____16844 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16859  ->
                 match uu____16859 with
                 | (bv,uu____16869) ->
                     let uu____16874 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____16874) Prims.int_zero bs
           in
        uu____16842 + uu____16844
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____16903 = sizeof hd  in
        let uu____16905 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____16920  ->
                 match uu____16920 with
                 | (arg,uu____16930) ->
                     let uu____16935 = sizeof arg  in acc + uu____16935)
            Prims.int_zero args
           in
        uu____16903 + uu____16905
    | uu____16938 -> Prims.int_one
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____16952 =
        let uu____16953 = un_uinst t  in uu____16953.FStar_Syntax_Syntax.n
         in
      match uu____16952 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16958 -> false
  
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
           let uu____17019 = head_and_args t  in
           match uu____17019 with
           | (head,args) ->
               let uu____17074 =
                 let uu____17075 = FStar_Syntax_Subst.compress head  in
                 uu____17075.FStar_Syntax_Syntax.n  in
               (match uu____17074 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____17101 -> FStar_Pervasives_Native.None)) attrs
  
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr  ->
    fun attrs  ->
      FStar_List.filter
        (fun a  ->
           let uu____17134 = is_fvar attr a  in Prims.op_Negation uu____17134)
        attrs
  
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options s =
        let uu____17155 = FStar_Options.set_options s  in
        match uu____17155 with
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
          ((let uu____17169 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____17169 (fun uu____17171  -> ()));
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
          let uu____17185 = FStar_Options.internal_pop ()  in
          if uu____17185
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
    | FStar_Syntax_Syntax.Tm_delayed uu____17217 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17236 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17251 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17252 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17253 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____17262) ->
        let uu____17287 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____17287 with
         | (bs1,t2) ->
             let uu____17296 =
               FStar_List.collect
                 (fun uu____17308  ->
                    match uu____17308 with
                    | (b,uu____17318) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17323 = unbound_variables t2  in
             FStar_List.append uu____17296 uu____17323)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____17348 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____17348 with
         | (bs1,c1) ->
             let uu____17357 =
               FStar_List.collect
                 (fun uu____17369  ->
                    match uu____17369 with
                    | (b,uu____17379) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____17384 = unbound_variables_comp c1  in
             FStar_List.append uu____17357 uu____17384)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____17393 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____17393 with
         | (bs,t2) ->
             let uu____17416 =
               FStar_List.collect
                 (fun uu____17428  ->
                    match uu____17428 with
                    | (b1,uu____17438) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____17443 = unbound_variables t2  in
             FStar_List.append uu____17416 uu____17443)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____17472 =
          FStar_List.collect
            (fun uu____17486  ->
               match uu____17486 with
               | (x,uu____17498) -> unbound_variables x) args
           in
        let uu____17507 = unbound_variables t1  in
        FStar_List.append uu____17472 uu____17507
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____17548 = unbound_variables t1  in
        let uu____17551 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____17566 = FStar_Syntax_Subst.open_branch br  in
                  match uu____17566 with
                  | (p,wopt,t2) ->
                      let uu____17588 = unbound_variables t2  in
                      let uu____17591 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____17588 uu____17591))
           in
        FStar_List.append uu____17548 uu____17551
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____17605) ->
        let uu____17646 = unbound_variables t1  in
        let uu____17649 =
          let uu____17652 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____17683 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____17652 uu____17683  in
        FStar_List.append uu____17646 uu____17649
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____17724 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____17727 =
          let uu____17730 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____17733 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17738 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____17740 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____17740 with
                 | (uu____17761,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____17730 uu____17733  in
        FStar_List.append uu____17724 uu____17727
    | FStar_Syntax_Syntax.Tm_let ((uu____17763,lbs),t1) ->
        let uu____17783 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____17783 with
         | (lbs1,t2) ->
             let uu____17798 = unbound_variables t2  in
             let uu____17801 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____17808 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____17811 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____17808 uu____17811) lbs1
                in
             FStar_List.append uu____17798 uu____17801)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____17828 = unbound_variables t1  in
        let uu____17831 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____17836,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____17891  ->
                      match uu____17891 with
                      | (a,uu____17903) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____17912,uu____17913,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____17919,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____17925 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____17934 -> []
          | FStar_Syntax_Syntax.Meta_named uu____17935 -> []  in
        FStar_List.append uu____17828 uu____17831

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____17942) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____17952) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17962 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____17965 =
          FStar_List.collect
            (fun uu____17979  ->
               match uu____17979 with
               | (a,uu____17991) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____17962 uu____17965

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
            let uu____18106 = head_and_args h  in
            (match uu____18106 with
             | (head,args) ->
                 let uu____18167 =
                   let uu____18168 = FStar_Syntax_Subst.compress head  in
                   uu____18168.FStar_Syntax_Syntax.n  in
                 (match uu____18167 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18221 -> aux (h :: acc) t))
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
      let uu____18245 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____18245 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2505_18287 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2505_18287.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2505_18287.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2505_18287.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2505_18287.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2505_18287.FStar_Syntax_Syntax.sigopts)
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18295 =
      let uu____18296 = FStar_Syntax_Subst.compress t  in
      uu____18296.FStar_Syntax_Syntax.n  in
    match uu____18295 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18300,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____18328)::uu____18329 ->
                  let pats' = unmeta pats  in
                  let uu____18389 = head_and_args pats'  in
                  (match uu____18389 with
                   | (head,uu____18408) ->
                       let uu____18433 =
                         let uu____18434 = un_uinst head  in
                         uu____18434.FStar_Syntax_Syntax.n  in
                       (match uu____18433 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18439 -> false))
              | uu____18441 -> false)
         | uu____18453 -> false)
    | uu____18455 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____18471 =
      let uu____18488 = unmeta e  in head_and_args uu____18488  in
    match uu____18471 with
    | (head,args) ->
        let uu____18519 =
          let uu____18534 =
            let uu____18535 = un_uinst head  in
            uu____18535.FStar_Syntax_Syntax.n  in
          (uu____18534, args)  in
        (match uu____18519 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____18553) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____18577::(hd,uu____18579)::(tl,uu____18581)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18648 =
               let uu____18651 =
                 let uu____18654 = list_elements tl  in
                 FStar_Util.must uu____18654  in
               hd :: uu____18651  in
             FStar_Pervasives_Native.Some uu____18648
         | uu____18663 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____18692 =
      let uu____18693 = FStar_Syntax_Subst.compress t  in
      uu____18693.FStar_Syntax_Syntax.n  in
    match uu____18692 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____18700) ->
        let uu____18735 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____18735 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____18769 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____18769
             then
               let uu____18776 =
                 let uu____18787 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____18787]  in
               mk_app t uu____18776
             else e1)
    | uu____18814 ->
        let uu____18815 =
          let uu____18826 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____18826]  in
        mk_app t uu____18815
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____18881 = list_elements e  in
        match uu____18881 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____18916 =
          let uu____18933 = unmeta p  in
          FStar_All.pipe_right uu____18933 head_and_args  in
        match uu____18916 with
        | (head,args) ->
            let uu____18984 =
              let uu____18999 =
                let uu____19000 = un_uinst head  in
                uu____19000.FStar_Syntax_Syntax.n  in
              (uu____18999, args)  in
            (match uu____18984 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____19022,uu____19023)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____19075 ->
                 let uu____19090 =
                   let uu____19096 =
                     let uu____19098 = tts p  in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____19098
                      in
                   (FStar_Errors.Error_IllSMTPat, uu____19096)  in
                 FStar_Errors.raise_error uu____19090
                   p.FStar_Syntax_Syntax.pos)
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____19141 =
            let uu____19158 = unmeta t1  in
            FStar_All.pipe_right uu____19158 head_and_args  in
          match uu____19141 with
          | (head,args) ->
              let uu____19205 =
                let uu____19220 =
                  let uu____19221 = un_uinst head  in
                  uu____19221.FStar_Syntax_Syntax.n  in
                (uu____19220, args)  in
              (match uu____19205 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____19240)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19277 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____19307 = smt_pat_or t1  in
            (match uu____19307 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19329 = list_elements1 e  in
                 FStar_All.pipe_right uu____19329
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____19359 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____19359
                           (FStar_List.map one_pat)))
             | uu____19388 ->
                 let uu____19393 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____19393])
        | uu____19448 ->
            let uu____19451 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____19451]
         in
      let uu____19506 =
        let uu____19539 =
          let uu____19540 = FStar_Syntax_Subst.compress t  in
          uu____19540.FStar_Syntax_Syntax.n  in
        match uu____19539 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____19597 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____19597 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19668;
                        FStar_Syntax_Syntax.effect_name = uu____19669;
                        FStar_Syntax_Syntax.result_typ = uu____19670;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____19672)::(post,uu____19674)::(pats,uu____19676)::[];
                        FStar_Syntax_Syntax.flags = uu____19677;_}
                      ->
                      let uu____19738 = lemma_pats pats  in
                      (binders1, pre, post, uu____19738)
                  | uu____19775 -> failwith "impos"))
        | uu____19809 -> failwith "Impos"  in
      match uu____19506 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____19901 =
              let uu____19908 =
                let uu____19909 =
                  let uu____19916 = mk_imp pre post1  in
                  let uu____19919 =
                    let uu____19920 =
                      let uu____19941 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____19941, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____19920  in
                  (uu____19916, uu____19919)  in
                FStar_Syntax_Syntax.Tm_meta uu____19909  in
              FStar_Syntax_Syntax.mk uu____19908  in
            uu____19901 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____19965 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____19965 body
             in
          quant
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____19995 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____20006 -> true
    | uu____20008 -> false
  
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____20019 -> true
    | uu____20021 -> false
  
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let uu____20039 = f combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____20040 = f combs.FStar_Syntax_Syntax.bind_wp  in
      let uu____20041 = f combs.FStar_Syntax_Syntax.stronger  in
      let uu____20042 = f combs.FStar_Syntax_Syntax.if_then_else  in
      let uu____20043 = f combs.FStar_Syntax_Syntax.ite_wp  in
      let uu____20044 = f combs.FStar_Syntax_Syntax.close_wp  in
      let uu____20045 = f combs.FStar_Syntax_Syntax.trivial  in
      let uu____20046 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr  in
      let uu____20049 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr  in
      let uu____20052 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr  in
      {
        FStar_Syntax_Syntax.ret_wp = uu____20039;
        FStar_Syntax_Syntax.bind_wp = uu____20040;
        FStar_Syntax_Syntax.stronger = uu____20041;
        FStar_Syntax_Syntax.if_then_else = uu____20042;
        FStar_Syntax_Syntax.ite_wp = uu____20043;
        FStar_Syntax_Syntax.close_wp = uu____20044;
        FStar_Syntax_Syntax.trivial = uu____20045;
        FStar_Syntax_Syntax.repr = uu____20046;
        FStar_Syntax_Syntax.return_repr = uu____20049;
        FStar_Syntax_Syntax.bind_repr = uu____20052
      }
  
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f  ->
    fun combs  ->
      let map_tuple uu____20084 =
        match uu____20084 with
        | (ts1,ts2) ->
            let uu____20095 = f ts1  in
            let uu____20096 = f ts2  in (uu____20095, uu____20096)
         in
      let uu____20097 = map_tuple combs.FStar_Syntax_Syntax.l_repr  in
      let uu____20102 = map_tuple combs.FStar_Syntax_Syntax.l_return  in
      let uu____20107 = map_tuple combs.FStar_Syntax_Syntax.l_bind  in
      let uu____20112 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp  in
      let uu____20117 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else
         in
      {
        FStar_Syntax_Syntax.l_base_effect =
          (combs.FStar_Syntax_Syntax.l_base_effect);
        FStar_Syntax_Syntax.l_repr = uu____20097;
        FStar_Syntax_Syntax.l_return = uu____20102;
        FStar_Syntax_Syntax.l_bind = uu____20107;
        FStar_Syntax_Syntax.l_subcomp = uu____20112;
        FStar_Syntax_Syntax.l_if_then_else = uu____20117
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
          let uu____20139 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Primitive_eff uu____20139
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____20141 = apply_wp_eff_combinators f combs1  in
          FStar_Syntax_Syntax.DM4F_eff uu____20141
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____20143 = apply_layered_eff_combinators f combs1  in
          FStar_Syntax_Syntax.Layered_eff uu____20143
  
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
    | uu____20158 -> FStar_Pervasives_Native.None
  
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
        let uu____20172 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20172
          (fun uu____20179  -> FStar_Pervasives_Native.Some uu____20179)
  
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
        let uu____20219 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20219
          (fun uu____20226  -> FStar_Pervasives_Native.Some uu____20226)
  
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
        let uu____20240 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20240
          (fun uu____20247  -> FStar_Pervasives_Native.Some uu____20247)
  
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20261  -> FStar_Pervasives_Native.Some uu____20261)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20265  -> FStar_Pervasives_Native.Some uu____20265)
    | uu____20266 -> FStar_Pervasives_Native.None
  
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20278 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20278
          (fun uu____20285  -> FStar_Pervasives_Native.Some uu____20285)
    | uu____20286 -> FStar_Pervasives_Native.None
  
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20300  -> FStar_Pervasives_Native.Some uu____20300)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20304  -> FStar_Pervasives_Native.Some uu____20304)
    | uu____20305 -> FStar_Pervasives_Native.None
  
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20319  -> FStar_Pervasives_Native.Some uu____20319)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20323  -> FStar_Pervasives_Native.Some uu____20323)
    | uu____20324 -> FStar_Pervasives_Native.None
  
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
    | FStar_Syntax_Syntax.Primitive_eff uu____20348 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20349 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20351 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst
           in
        FStar_All.pipe_right uu____20351
          (fun uu____20358  -> FStar_Pervasives_Native.Some uu____20358)
  
let (get_layered_effect_base :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun ed  ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect
          (fun uu____20372  -> FStar_Pervasives_Native.Some uu____20372)
    | uu____20373 -> FStar_Pervasives_Native.None
  