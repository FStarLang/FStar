open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____46 = FStar_ST.op_Bang tts_f  in
    match uu____46 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____150 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____150 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____185 =
      let uu____190 =
        let uu____195 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____195]  in
      FStar_List.append lid.FStar_Ident.ns uu____190  in
    FStar_Ident.lid_of_ids uu____185
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____231 .
    (FStar_Syntax_Syntax.bv * 'Auu____231) ->
      (FStar_Syntax_Syntax.term * 'Auu____231)
  =
  fun uu____253  ->
    match uu____253 with
    | (b,imp) ->
        let uu____275 = FStar_Syntax_Syntax.bv_to_name b  in (uu____275, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____366 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____366
            then []
            else (let uu____393 = arg_of_non_null_binder b  in [uu____393])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____440 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____564 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____564
              then
                let b1 =
                  let uu____604 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____604, (FStar_Pervasives_Native.snd b))  in
                let uu____636 = arg_of_non_null_binder b1  in (b1, uu____636)
              else
                (let uu____672 = arg_of_non_null_binder b  in (b, uu____672))))
       in
    FStar_All.pipe_right uu____440 FStar_List.unzip
  
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
              let uu____877 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____877
              then
                let uu____891 = b  in
                match uu____891 with
                | (a,imp) ->
                    let b1 =
                      let uu____935 =
                        let uu____937 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____937  in
                      FStar_Ident.id_of_text uu____935  in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = (Prims.parse_int "0");
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
        let uu____1031 =
          let uu____1038 =
            let uu____1039 =
              let uu____1063 = name_binders binders  in (uu____1063, comp)
               in
            FStar_Syntax_Syntax.Tm_arrow uu____1039  in
          FStar_Syntax_Syntax.mk uu____1038  in
        uu____1031 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____1096 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____1154  ->
            match uu____1154 with
            | (t,imp) ->
                let uu____1182 =
                  let uu____1193 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1193
                   in
                (uu____1182, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____1294  ->
            match uu____1294 with
            | (t,imp) ->
                let uu____1328 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____1328, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____1366 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____1366
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____1398 . 'Auu____1398 -> 'Auu____1398 Prims.list =
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
          (fun uu____1589  ->
             fun uu____1590  ->
               match (uu____1589, uu____1590) with
               | ((x,uu____1636),(y,uu____1638)) ->
                   let uu____1689 =
                     let uu____1705 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____1705)  in
                   FStar_Syntax_Syntax.NT uu____1689) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____1762) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1776,uu____1777) -> unmeta e2
    | uu____1858 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____1908 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____1923 -> e1
         | uu____1944 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1946,uu____1947) ->
        unmeta_safe e2
    | uu____2028 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____2047 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____2052 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____2068 = univ_kernel u1  in
        (match uu____2068 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____2085 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____2094 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____2109 = univ_kernel u  in FStar_Pervasives_Native.snd uu____2109
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____2129,uu____2130) ->
          failwith "Impossible: compare_univs"
      | (uu____2134,FStar_Syntax_Syntax.U_bvar uu____2135) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____2140) ->
          ~- (Prims.parse_int "1")
      | (uu____2142,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____2145) -> ~- (Prims.parse_int "1")
      | (uu____2147,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____2155,FStar_Syntax_Syntax.U_unif
         uu____2156) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____2170,FStar_Syntax_Syntax.U_name
         uu____2171) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____2207 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____2209 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____2207 - uu____2209
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____2227 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____2227
                 (fun uu____2243  ->
                    match uu____2243 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____2271,uu____2272) ->
          ~- (Prims.parse_int "1")
      | (uu____2276,FStar_Syntax_Syntax.U_max uu____2277) ->
          (Prims.parse_int "1")
      | uu____2281 ->
          let uu____2286 = univ_kernel u1  in
          (match uu____2286 with
           | (k1,n1) ->
               let uu____2297 = univ_kernel u2  in
               (match uu____2297 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____2328 = compare_univs u1 u2  in
      uu____2328 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____2359 =
        let uu____2370 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____2370;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____2359
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____2431 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____2444 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2479 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____2492 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____2559 =
          let uu____2560 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____2560  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____2559;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____2601 =
          let uu____2602 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____2602  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____2601;
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
      let uu___229_2654 = c  in
      let uu____2663 =
        let uu____2664 =
          let uu___231_2675 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___231_2675.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___231_2675.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___231_2675.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___231_2675.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____2664  in
      {
        FStar_Syntax_Syntax.n = uu____2663;
        FStar_Syntax_Syntax.pos = (uu___229_2654.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___229_2654.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2759 -> c
        | FStar_Syntax_Syntax.GTotal uu____2772 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___243_2802 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___243_2802.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___243_2802.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___243_2802.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___243_2802.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___246_2813 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___246_2813.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___246_2813.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____2824  ->
           let uu____2825 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____2825)
  
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
    | uu____2920 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____2953 -> true
    | FStar_Syntax_Syntax.GTotal uu____2967 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_3004  ->
               match uu___0_3004 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3008 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___1_3037  ->
               match uu___1_3037 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3041 -> false)))
  
let (is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
        FStar_Parser_Const.effect_Tot_lid)
       ||
       (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
          FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___2_3070  ->
               match uu___2_3070 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3074 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___3_3099  ->
            match uu___3_3099 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____3103 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___4_3132  ->
            match uu___4_3132 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____3136 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____3192 -> true
    | FStar_Syntax_Syntax.GTotal uu____3206 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___5_3230  ->
                   match uu___5_3230 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____3233 -> false)))
  
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
let (is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___6_3326  ->
               match uu___6_3326 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____3329 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3369 =
      let uu____3370 = FStar_Syntax_Subst.compress t  in
      uu____3370.FStar_Syntax_Syntax.n  in
    match uu____3369 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____3382,c) -> is_pure_or_ghost_comp c
    | uu____3422 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____3450 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3467 =
      let uu____3468 = FStar_Syntax_Subst.compress t  in
      uu____3468.FStar_Syntax_Syntax.n  in
    match uu____3467 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____3480,c) -> is_lemma_comp c
    | uu____3520 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3544 =
      let uu____3545 = FStar_Syntax_Subst.compress t  in
      uu____3545.FStar_Syntax_Syntax.n  in
    match uu____3544 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____3561) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____3603) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____3670,t1,uu____3672) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3730,uu____3731) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3813) -> head_of t1
    | uu____3826 -> t
  
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
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____3960 -> (t1, [])
  
let rec (head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____4102 = head_and_args' head1  in
        (match uu____4102 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____4215 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4278) ->
        FStar_Syntax_Subst.compress t2
    | uu____4291 -> t1
  
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
                (fun uu___7_4322  ->
                   match uu___7_4322 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____4325 -> false)))
    | uu____4327 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4368) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____4386) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____4452 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____4465 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___399_4486 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___399_4486.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___399_4486.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___399_4486.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___399_4486.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4550  ->
           let uu____4551 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____4551 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___8_4585  ->
            match uu___8_4585 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____4589 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____4605 -> []
    | FStar_Syntax_Syntax.GTotal uu____4630 -> []
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
    | uu____4786 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____4820,uu____4821) ->
        unascribe e2
    | uu____4902 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____4995,uu____4996) ->
          ascribe t' k
      | uu____5077 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____5140 =
      let uu____5157 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____5157  in
    uu____5140 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____5257 =
      let uu____5258 = FStar_Syntax_Subst.compress t  in
      uu____5258.FStar_Syntax_Syntax.n  in
    match uu____5257 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____5278 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____5278
    | uu____5295 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____5314 =
      let uu____5315 = FStar_Syntax_Subst.compress t  in
      uu____5315.FStar_Syntax_Syntax.n  in
    match uu____5314 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____5339 ->
             let uu____5352 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____5352
         | uu____5369 -> t)
    | uu____5370 -> t
  
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
      | uu____5394 -> false
  
let rec unlazy_as_t :
  'Auu____5407 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'Auu____5407
  =
  fun k  ->
    fun t  ->
      let uu____5426 =
        let uu____5427 = FStar_Syntax_Subst.compress t  in
        uu____5427.FStar_Syntax_Syntax.n  in
      match uu____5426 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____5440;
            FStar_Syntax_Syntax.rng = uu____5441;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____5448 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____5509 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____5509;
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
    let uu____5534 =
      let uu____5557 = unascribe t  in head_and_args' uu____5557  in
    match uu____5534 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____5619 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____5630 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____5641 -> false
  
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
      | (NotEqual ,uu____5691) -> NotEqual
      | (uu____5692,NotEqual ) -> NotEqual
      | (Unknown ,uu____5693) -> Unknown
      | (uu____5694,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___9_5891 = if uu___9_5891 then Equal else Unknown  in
      let equal_iff uu___10_5902 = if uu___10_5902 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____5923 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____5957 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____5957
        then
          let uu____5961 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____6070  ->
                    match uu____6070 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____6143 = eq_tm a1 a2  in
                        eq_inj acc uu____6143) Equal) uu____5961
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____6163 =
          let uu____6188 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____6188 head_and_args  in
        match uu____6163 with
        | (head1,args1) ->
            let uu____6291 =
              let uu____6316 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____6316 head_and_args  in
            (match uu____6291 with
             | (head2,args2) ->
                 let uu____6419 =
                   let uu____6424 =
                     let uu____6425 = un_uinst head1  in
                     uu____6425.FStar_Syntax_Syntax.n  in
                   let uu____6436 =
                     let uu____6437 = un_uinst head2  in
                     uu____6437.FStar_Syntax_Syntax.n  in
                   (uu____6424, uu____6436)  in
                 (match uu____6419 with
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
                  | uu____6496 -> FStar_Pervasives_Native.None))
         in
      let uu____6515 =
        let uu____6520 =
          let uu____6521 = unmeta t11  in uu____6521.FStar_Syntax_Syntax.n
           in
        let uu____6532 =
          let uu____6533 = unmeta t21  in uu____6533.FStar_Syntax_Syntax.n
           in
        (uu____6520, uu____6532)  in
      match uu____6515 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____6557,uu____6558) ->
          let uu____6563 = unlazy t11  in eq_tm uu____6563 t21
      | (uu____6572,FStar_Syntax_Syntax.Tm_lazy uu____6573) ->
          let uu____6578 = unlazy t21  in eq_tm t11 uu____6578
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____6599 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____6635 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____6635
            (fun uu____6713  ->
               match uu____6713 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____6752 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____6752
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____6782 = eq_tm f g  in
          eq_and uu____6782
            (fun uu____6785  ->
               let uu____6786 = eq_univs_list us vs  in equal_if uu____6786)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____6788),uu____6789) -> Unknown
      | (uu____6790,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____6791)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____6794 = FStar_Const.eq_const c d  in equal_iff uu____6794
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____6797)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____6799))) ->
          let uu____6860 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____6860
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____6946 =
            let uu____6951 =
              let uu____6952 = un_uinst h1  in
              uu____6952.FStar_Syntax_Syntax.n  in
            let uu____6963 =
              let uu____6964 = un_uinst h2  in
              uu____6964.FStar_Syntax_Syntax.n  in
            (uu____6951, uu____6963)  in
          (match uu____6946 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____6984 =
                    let uu____6986 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____6986  in
                  FStar_List.mem uu____6984 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____6996 ->
               let uu____7001 = eq_tm h1 h2  in
               eq_and uu____7001 (fun uu____7003  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____7191 = FStar_List.zip bs1 bs2  in
            let uu____7298 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____7357  ->
                 fun a  ->
                   match uu____7357 with
                   | (b1,b2) ->
                       eq_and a (fun uu____7510  -> branch_matches b1 b2))
              uu____7191 uu____7298
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____7515 = eq_univs u v1  in equal_if uu____7515
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____7553 = eq_quoteinfo q1 q2  in
          eq_and uu____7553 (fun uu____7555  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____7604 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____7604 (fun uu____7606  -> eq_tm phi1 phi2)
      | uu____7607 -> Unknown

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
      | ([],uu____7755) -> NotEqual
      | (uu____7822,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____8040 = eq_tm t1 t2  in
             match uu____8040 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____8041 = eq_antiquotes a11 a21  in
                 (match uu____8041 with
                  | NotEqual  -> NotEqual
                  | uu____8042 -> Unknown)
             | Equal  -> eq_antiquotes a11 a21)

and (eq_aqual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      eq_result)
  =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          Equal
      | (FStar_Pervasives_Native.None ,uu____8057) -> NotEqual
      | (uu____8064,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____8102 -> NotEqual

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
        | (uu____8290,uu____8291) -> false  in
      let uu____8317 = b1  in
      match uu____8317 with
      | (p1,w1,t1) ->
          let uu____8384 = b2  in
          (match uu____8384 with
           | (p2,w2,t2) ->
               let uu____8451 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____8451
               then
                 let uu____8454 =
                   (let uu____8458 = eq_tm t1 t2  in uu____8458 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____8475 = eq_tm t11 t21  in
                             uu____8475 = Equal) w1 w2)
                    in
                 (if uu____8454 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____8564)::a11,(b,uu____8567)::b1) ->
          let uu____8681 = eq_tm a b  in
          (match uu____8681 with
           | Equal  -> eq_args a11 b1
           | uu____8682 -> Unknown)
      | uu____8683 -> Unknown

and (eq_univs_list :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool)
  =
  fun us  ->
    fun vs  ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)

let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____8751) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____8775,uu____8776) ->
        unrefine t2
    | uu____8857 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8873 =
      let uu____8874 = FStar_Syntax_Subst.compress t  in
      uu____8874.FStar_Syntax_Syntax.n  in
    match uu____8873 with
    | FStar_Syntax_Syntax.Tm_uvar uu____8886 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____8909) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____8922 ->
        let uu____8947 =
          let uu____8956 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____8956 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____8947 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____9063,uu____9064) ->
        is_uvar t1
    | uu____9145 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9162 =
      let uu____9163 = unrefine t  in uu____9163.FStar_Syntax_Syntax.n  in
    match uu____9162 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____9180) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9222) -> is_unit t1
    | uu____9235 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9252 =
      let uu____9253 = FStar_Syntax_Subst.compress t  in
      uu____9253.FStar_Syntax_Syntax.n  in
    match uu____9252 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____9269 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9286 =
      let uu____9287 = unrefine t  in uu____9287.FStar_Syntax_Syntax.n  in
    match uu____9286 with
    | FStar_Syntax_Syntax.Tm_type uu____9299 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____9306) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9348) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____9361,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____9401 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____9418 =
      let uu____9419 = FStar_Syntax_Subst.compress e  in
      uu____9419.FStar_Syntax_Syntax.n  in
    match uu____9418 with
    | FStar_Syntax_Syntax.Tm_abs uu____9431 -> true
    | uu____9467 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9484 =
      let uu____9485 = FStar_Syntax_Subst.compress t  in
      uu____9485.FStar_Syntax_Syntax.n  in
    match uu____9484 with
    | FStar_Syntax_Syntax.Tm_arrow uu____9497 -> true
    | uu____9522 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____9556) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____9580,uu____9581) ->
        pre_typ t2
    | uu____9662 -> t1
  
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
      let uu____9715 =
        let uu____9716 = un_uinst typ1  in uu____9716.FStar_Syntax_Syntax.n
         in
      match uu____9715 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____9828 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____9873 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____9916,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____9931) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____9952,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____9981,uu____9982,uu____9983,uu____9984,uu____9985) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____10035,uu____10036,uu____10037,uu____10038) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____10068,uu____10069,uu____10070,uu____10071,uu____10072) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____10120,uu____10121) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____10147,uu____10148) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____10231 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____10244 -> []
    | FStar_Syntax_Syntax.Sig_main uu____10249 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____10309 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___11_10371  ->
    match uu___11_10371 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____10421 'Auu____10422 .
    ('Auu____10421 FStar_Syntax_Syntax.syntax * 'Auu____10422) ->
      FStar_Range.range
  =
  fun uu____10437  ->
    match uu____10437 with | (hd1,uu____10449) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____10471 'Auu____10472 .
    ('Auu____10471 FStar_Syntax_Syntax.syntax * 'Auu____10472) Prims.list ->
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
      | uu____10618 ->
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
      let uu____10711 =
        FStar_List.map
          (fun uu____10751  ->
             match uu____10751 with
             | (bv,aq) ->
                 let uu____10789 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____10789, aq)) bs
         in
      mk_app f uu____10711
  
let (mk_data :
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Syntax_Syntax.syntax)
  =
  fun l  ->
    fun args  ->
      match args with
      | [] ->
          let uu____10887 = FStar_Ident.range_of_lid l  in
          let uu____10888 =
            let uu____10901 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____10901  in
          uu____10888 FStar_Pervasives_Native.None uu____10887
      | uu____10918 ->
          let e =
            let uu____10944 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____10944 args  in
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
  
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
      let itext = i.FStar_Ident.idText  in
      let newi =
        if field_projector_contains_constructor itext
        then i
        else
          FStar_Ident.mk_ident
            ((mk_field_projector_name_from_string
                (lid.FStar_Ident.ident).FStar_Ident.idText itext),
              (i.FStar_Ident.idRange))
         in
      FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns [newi])
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv ->
      Prims.int -> (FStar_Ident.lident * FStar_Syntax_Syntax.bv))
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____11092 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____11092
          then
            let uu____11097 =
              let uu____11103 =
                let uu____11105 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____11105  in
              let uu____11108 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____11103, uu____11108)  in
            FStar_Ident.mk_ident uu____11097
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___993_11123 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___993_11123.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___993_11123.FStar_Syntax_Syntax.sort)
          }  in
        let uu____11134 = mk_field_projector_name_from_ident lid nm  in
        (uu____11134, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11183) -> ses
    | uu____11210 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____11296 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____11337 = FStar_Syntax_Unionfind.find uv  in
      match uu____11337 with
      | FStar_Pervasives_Native.Some uu____11344 ->
          let uu____11353 =
            let uu____11355 =
              let uu____11357 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____11357  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____11355  in
          failwith uu____11353
      | uu____11362 -> FStar_Syntax_Unionfind.change uv t
  
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
            (l1b.FStar_Ident.idText = l2b.FStar_Ident.idText)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
                 f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
               f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
                 f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
               f1 f2)
      | uu____11561 -> q1 = q2
  
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
              let uu____11689 =
                let uu___1054_11704 = rc  in
                let uu____11719 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1054_11704.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____11719;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1054_11704.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____11689
           in
        match bs with
        | [] -> t
        | uu____11764 ->
            let body =
              let uu____11774 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____11774  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____11848 =
                   let uu____11855 =
                     let uu____11856 =
                       let uu____11891 =
                         let uu____11905 =
                           FStar_Syntax_Subst.close_binders bs  in
                         FStar_List.append uu____11905 bs'  in
                       let uu____11930 = close_lopt lopt'  in
                       (uu____11891, t1, uu____11930)  in
                     FStar_Syntax_Syntax.Tm_abs uu____11856  in
                   FStar_Syntax_Syntax.mk uu____11855  in
                 uu____11848 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____11968 ->
                 let uu____11969 =
                   let uu____11976 =
                     let uu____11977 =
                       let uu____12012 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____12026 = close_lopt lopt  in
                       (uu____12012, body, uu____12026)  in
                     FStar_Syntax_Syntax.Tm_abs uu____11977  in
                   FStar_Syntax_Syntax.mk uu____11976  in
                 uu____11969 FStar_Pervasives_Native.None
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
      | uu____12136 ->
          let uu____12150 =
            let uu____12157 =
              let uu____12158 =
                let uu____12182 = FStar_Syntax_Subst.close_binders bs  in
                let uu____12196 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____12182, uu____12196)  in
              FStar_Syntax_Syntax.Tm_arrow uu____12158  in
            FStar_Syntax_Syntax.mk uu____12157  in
          uu____12150 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____12292 =
        let uu____12293 = FStar_Syntax_Subst.compress t  in
        uu____12293.FStar_Syntax_Syntax.n  in
      match uu____12292 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____12357) ->
               let uu____12374 =
                 let uu____12375 = FStar_Syntax_Subst.compress tres  in
                 uu____12375.FStar_Syntax_Syntax.n  in
               (match uu____12374 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____12462 -> t)
           | uu____12463 -> t)
      | uu____12464 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____12504 =
        let uu____12505 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____12505 t.FStar_Syntax_Syntax.pos  in
      let uu____12506 =
        let uu____12513 =
          let uu____12514 =
            let uu____12530 =
              let uu____12541 =
                let uu____12542 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____12542]  in
              FStar_Syntax_Subst.close uu____12541 t  in
            (b, uu____12530)  in
          FStar_Syntax_Syntax.Tm_refine uu____12514  in
        FStar_Syntax_Syntax.mk uu____12513  in
      uu____12506 FStar_Pervasives_Native.None uu____12504
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____12698 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____12698 with
         | (bs1,c1) ->
             let uu____12738 = is_total_comp c1  in
             if uu____12738
             then
               let uu____12762 = arrow_formals_comp (comp_result c1)  in
               (match uu____12762 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____12888;
           FStar_Syntax_Syntax.index = uu____12889;
           FStar_Syntax_Syntax.sort = s;_},uu____12891)
        ->
        let rec aux s1 k2 =
          let uu____12966 =
            let uu____12967 = FStar_Syntax_Subst.compress s1  in
            uu____12967.FStar_Syntax_Syntax.n  in
          match uu____12966 with
          | FStar_Syntax_Syntax.Tm_arrow uu____12999 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____13023;
                 FStar_Syntax_Syntax.index = uu____13024;
                 FStar_Syntax_Syntax.sort = s2;_},uu____13026)
              -> aux s2 k2
          | uu____13053 ->
              let uu____13054 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____13054)
           in
        aux s k1
    | uu____13091 ->
        let uu____13092 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____13092)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____13166 = arrow_formals_comp k  in
    match uu____13166 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____13419 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____13419 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____13474 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___12_13483  ->
                         match uu___12_13483 with
                         | FStar_Syntax_Syntax.DECREASES uu____13485 -> true
                         | uu____13493 -> false))
                  in
               (match uu____13474 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____13554 ->
                    let uu____13557 = is_total_comp c1  in
                    if uu____13557
                    then
                      let uu____13585 =
                        arrow_until_decreases (comp_result c1)  in
                      (match uu____13585 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____13741;
             FStar_Syntax_Syntax.index = uu____13742;
             FStar_Syntax_Syntax.sort = k2;_},uu____13744)
          -> arrow_until_decreases k2
      | uu____13771 -> ([], FStar_Pervasives_Native.None)  in
    let uu____13810 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____13810 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____13893 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____13927 =
                 FStar_Common.tabulate n_univs (fun uu____13933  -> false)
                  in
               let uu____13936 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____13971  ->
                         match uu____13971 with
                         | (x,uu____13985) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____13927 uu____13936)
           in
        ((n_univs + (FStar_List.length bs)), uu____13893)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____14122 =
            let uu___1176_14137 = rc  in
            let uu____14152 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1176_14137.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____14152;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1176_14137.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____14122
      | uu____14180 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____14259 =
        let uu____14260 =
          let uu____14271 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____14271  in
        uu____14260.FStar_Syntax_Syntax.n  in
      match uu____14259 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____14381 = aux t2 what  in
          (match uu____14381 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____14538 -> ([], t1, abs_body_lcomp)  in
    let uu____14576 = aux t FStar_Pervasives_Native.None  in
    match uu____14576 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____14690 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____14690 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
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
                    | (FStar_Pervasives_Native.None ,uu____15049) -> def
                    | (uu____15070,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____15092) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _15125  ->
                                  FStar_Syntax_Syntax.U_name _15125))
                           in
                        let inst1 =
                          FStar_All.pipe_right fvs
                            (FStar_List.map
                               (fun fv  ->
                                  (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                    universes)))
                           in
                        FStar_Syntax_InstFV.instantiate inst1 def
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
            let uu____15285 = FStar_Syntax_Subst.open_univ_vars_comp uvs c
               in
            (match uu____15285 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____15355 ->
            let t' = arrow binders c  in
            let uu____15380 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____15380 with
             | (uvs1,t'1) ->
                 let uu____15422 =
                   let uu____15423 = FStar_Syntax_Subst.compress t'1  in
                   uu____15423.FStar_Syntax_Syntax.n  in
                 (match uu____15422 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____15516 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____15565 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____15591 -> false
  
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
      let uu____15757 =
        let uu____15758 = pre_typ t  in uu____15758.FStar_Syntax_Syntax.n  in
      match uu____15757 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____15778 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____15808 =
        let uu____15809 = pre_typ t  in uu____15809.FStar_Syntax_Syntax.n  in
      match uu____15808 with
      | FStar_Syntax_Syntax.Tm_fvar uu____15821 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____15826) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____15868) ->
          is_constructed_typ t1 lid
      | uu____15881 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____15918 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____15928 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____15938 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____15947) -> get_tycon t2
    | uu____15988 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____16008 =
      let uu____16009 = un_uinst t  in uu____16009.FStar_Syntax_Syntax.n  in
    match uu____16008 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____16025 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____16047 =
        let uu____16051 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____16051  in
      match uu____16047 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____16083 -> false
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
  fun uu____16122  ->
    let u =
      let uu____16132 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _16153  -> FStar_Syntax_Syntax.U_unif _16153)
        uu____16132
       in
    let uu____16154 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____16154, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____16195 = eq_tm a a'  in
      match uu____16195 with | Equal  -> true | uu____16198 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____16211 =
    let uu____16218 =
      let uu____16219 =
        let uu____16226 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____16226
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____16219  in
    FStar_Syntax_Syntax.mk uu____16218  in
  uu____16211 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (tiff : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "2"))
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
          let uu____16558 =
            let uu____16569 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____16570 =
              let uu____16577 =
                let uu____16578 =
                  let uu____16603 =
                    let uu____16618 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____16631 =
                      let uu____16646 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____16646]  in
                    uu____16618 :: uu____16631  in
                  (tand, uu____16603)  in
                FStar_Syntax_Syntax.Tm_app uu____16578  in
              FStar_Syntax_Syntax.mk uu____16577  in
            uu____16570 FStar_Pervasives_Native.None uu____16569  in
          FStar_Pervasives_Native.Some uu____16558
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____16779 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____16780 =
          let uu____16787 =
            let uu____16788 =
              let uu____16813 =
                let uu____16828 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____16841 =
                  let uu____16856 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____16856]  in
                uu____16828 :: uu____16841  in
              (op_t, uu____16813)  in
            FStar_Syntax_Syntax.Tm_app uu____16788  in
          FStar_Syntax_Syntax.mk uu____16787  in
        uu____16780 FStar_Pervasives_Native.None uu____16779
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____16949 =
      let uu____16956 =
        let uu____16957 =
          let uu____16982 =
            let uu____16997 = FStar_Syntax_Syntax.as_arg phi  in
            [uu____16997]  in
          (t_not, uu____16982)  in
        FStar_Syntax_Syntax.Tm_app uu____16957  in
      FStar_Syntax_Syntax.mk uu____16956  in
    uu____16949 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
  
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
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
  
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
    let uu____17394 =
      let uu____17401 =
        let uu____17402 =
          let uu____17427 =
            let uu____17442 = FStar_Syntax_Syntax.as_arg e  in [uu____17442]
             in
          (b2t_v, uu____17427)  in
        FStar_Syntax_Syntax.Tm_app uu____17402  in
      FStar_Syntax_Syntax.mk uu____17401  in
    uu____17394 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____17525 = head_and_args e  in
    match uu____17525 with
    | (hd1,args) ->
        let uu____17598 =
          let uu____17617 =
            let uu____17618 = FStar_Syntax_Subst.compress hd1  in
            uu____17618.FStar_Syntax_Syntax.n  in
          (uu____17617, args)  in
        (match uu____17598 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(e1,uu____17651)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____17713 -> FStar_Pervasives_Native.None)
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____17751 =
      let uu____17752 = unmeta t  in uu____17752.FStar_Syntax_Syntax.n  in
    match uu____17751 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____17768 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____17811 = is_t_true t1  in
      if uu____17811
      then t2
      else
        (let uu____17822 = is_t_true t2  in
         if uu____17822 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____17874 = is_t_true t1  in
      if uu____17874
      then t_true
      else
        (let uu____17885 = is_t_true t2  in
         if uu____17885 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____17946 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____17947 =
        let uu____17954 =
          let uu____17955 =
            let uu____17980 =
              let uu____17995 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____18008 =
                let uu____18023 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____18023]  in
              uu____17995 :: uu____18008  in
            (teq, uu____17980)  in
          FStar_Syntax_Syntax.Tm_app uu____17955  in
        FStar_Syntax_Syntax.mk uu____17954  in
      uu____17947 FStar_Pervasives_Native.None uu____17946
  
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
          let uu____18154 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____18155 =
            let uu____18162 =
              let uu____18163 =
                let uu____18188 =
                  let uu____18203 = FStar_Syntax_Syntax.iarg t  in
                  let uu____18216 =
                    let uu____18231 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____18244 =
                      let uu____18259 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____18259]  in
                    uu____18231 :: uu____18244  in
                  uu____18203 :: uu____18216  in
                (eq_inst, uu____18188)  in
              FStar_Syntax_Syntax.Tm_app uu____18163  in
            FStar_Syntax_Syntax.mk uu____18162  in
          uu____18155 FStar_Pervasives_Native.None uu____18154
  
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
        let uu____18412 =
          let uu____18419 =
            let uu____18420 =
              let uu____18445 =
                let uu____18460 = FStar_Syntax_Syntax.iarg t  in
                let uu____18473 =
                  let uu____18488 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____18501 =
                    let uu____18516 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____18516]  in
                  uu____18488 :: uu____18501  in
                uu____18460 :: uu____18473  in
              (t_has_type1, uu____18445)  in
            FStar_Syntax_Syntax.Tm_app uu____18420  in
          FStar_Syntax_Syntax.mk uu____18419  in
        uu____18412 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____18661 =
          let uu____18668 =
            let uu____18669 =
              let uu____18694 =
                let uu____18709 = FStar_Syntax_Syntax.iarg t  in
                let uu____18722 =
                  let uu____18737 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____18737]  in
                uu____18709 :: uu____18722  in
              (t_with_type1, uu____18694)  in
            FStar_Syntax_Syntax.Tm_app uu____18669  in
          FStar_Syntax_Syntax.mk uu____18668  in
        uu____18661 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____18824 =
    let uu____18831 =
      let uu____18832 =
        let uu____18843 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____18843, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____18832  in
    FStar_Syntax_Syntax.mk uu____18831  in
  uu____18824 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (lex_pair : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (tforall : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (t_haseq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
  
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.lcomp) =
  fun c0  ->
    let uu____18910 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18931 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____18950 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____18910 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____19004  -> c0)
  
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
  
let (residual_comp_of_lcomp :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.residual_comp) =
  fun lc  ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.FStar_Syntax_Syntax.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.FStar_Syntax_Syntax.cflags)
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
        let uu____19261 =
          let uu____19268 =
            let uu____19269 =
              let uu____19294 =
                let uu____19309 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____19322 =
                  let uu____19337 =
                    let uu____19350 =
                      let uu____19359 =
                        let uu____19360 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____19360]  in
                      abs uu____19359 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____19350  in
                  [uu____19337]  in
                uu____19309 :: uu____19322  in
              (fa, uu____19294)  in
            FStar_Syntax_Syntax.Tm_app uu____19269  in
          FStar_Syntax_Syntax.mk uu____19268  in
        uu____19261 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____19629 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____19629
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____19660 -> true
    | uu____19667 -> false
  
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
          let uu____19753 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____19753, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____19811 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____19811, FStar_Pervasives_Native.None, t2)  in
        let uu____19843 =
          let uu____19844 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____19844  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____19843
  
let (mk_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "1"))
          FStar_Pervasives_Native.None
         in
      let uu____19988 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____19999 =
        let uu____20014 = FStar_Syntax_Syntax.as_arg p  in [uu____20014]  in
      mk_app uu____19988 uu____19999
  
let (mk_auto_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "2"))
          FStar_Pervasives_Native.None
         in
      let uu____20086 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____20097 =
        let uu____20112 = FStar_Syntax_Syntax.as_arg p  in [uu____20112]  in
      mk_app uu____20086 uu____20097
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____20171 = head_and_args t  in
    match uu____20171 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____20264 =
          let uu____20283 =
            let uu____20284 = FStar_Syntax_Subst.compress head3  in
            uu____20284.FStar_Syntax_Syntax.n  in
          (uu____20283, args)  in
        (match uu____20264 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____20319)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____20445 =
                    let uu____20454 =
                      let uu____20455 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____20455]  in
                    FStar_Syntax_Subst.open_term uu____20454 p  in
                  (match uu____20445 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____20564 -> failwith "impossible"  in
                       let uu____20577 =
                         let uu____20579 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____20579
                          in
                       if uu____20577
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____20622 -> FStar_Pervasives_Native.None)
         | uu____20629 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____20680 = head_and_args t  in
    match uu____20680 with
    | (head1,args) ->
        let uu____20759 =
          let uu____20778 =
            let uu____20779 = FStar_Syntax_Subst.compress head1  in
            uu____20779.FStar_Syntax_Syntax.n  in
          (uu____20778, args)  in
        (match uu____20759 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____20817;
               FStar_Syntax_Syntax.vars = uu____20818;_},u::[]),(t1,uu____20821)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____20907 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____20962 = head_and_args t  in
    match uu____20962 with
    | (head1,args) ->
        let uu____21041 =
          let uu____21060 =
            let uu____21061 = FStar_Syntax_Subst.compress head1  in
            uu____21061.FStar_Syntax_Syntax.n  in
          (uu____21060, args)  in
        (match uu____21041 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____21099;
               FStar_Syntax_Syntax.vars = uu____21100;_},u::[]),(t1,uu____21103)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____21189 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____21233 =
      let uu____21258 = unmeta t  in head_and_args uu____21258  in
    match uu____21233 with
    | (head1,uu____21269) ->
        let uu____21310 =
          let uu____21311 = un_uinst head1  in
          uu____21311.FStar_Syntax_Syntax.n  in
        (match uu____21310 with
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
         | uu____21327 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____21363 =
      let uu____21385 =
        let uu____21386 = FStar_Syntax_Subst.compress t  in
        uu____21386.FStar_Syntax_Syntax.n  in
      match uu____21385 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____21634 =
            let uu____21654 =
              let uu____21663 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____21663  in
            (b, uu____21654)  in
          FStar_Pervasives_Native.Some uu____21634
      | uu____21706 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____21363
      (fun uu____21771  ->
         match uu____21771 with
         | (b,c) ->
             let uu____21844 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____21844 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____21963 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____22041 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____22041
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____22119 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____22178 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____22235 -> false
  
let (__proj__BaseConn__item___0 :
  connective -> (FStar_Ident.lident * FStar_Syntax_Syntax.args)) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0 
let (destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1  in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____22318) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____22346) ->
          unmeta_monadic t
      | uu____22379 -> f2  in
    let destruct_base_conn f1 =
      let connectives =
        [(FStar_Parser_Const.true_lid, (Prims.parse_int "0"));
        (FStar_Parser_Const.false_lid, (Prims.parse_int "0"));
        (FStar_Parser_Const.and_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.or_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.imp_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.iff_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.ite_lid, (Prims.parse_int "3"));
        (FStar_Parser_Const.not_lid, (Prims.parse_int "1"));
        (FStar_Parser_Const.eq2_lid, (Prims.parse_int "3"));
        (FStar_Parser_Const.eq2_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.eq3_lid, (Prims.parse_int "4"));
        (FStar_Parser_Const.eq3_lid, (Prims.parse_int "2"))]  in
      let aux f2 uu____22595 =
        match uu____22595 with
        | (lid,arity) ->
            let uu____22620 =
              let uu____22645 = unmeta_monadic f2  in
              head_and_args uu____22645  in
            (match uu____22620 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____22707 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____22707
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (uu____22810,pats)) ->
          let uu____22872 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____22872)
      | uu____22901 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____23018 = head_and_args t1  in
        match uu____23018 with
        | (t2,args) ->
            let uu____23105 = un_uinst t2  in
            let uu____23114 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____23175  ->
                      match uu____23175 with
                      | (t3,imp) ->
                          let uu____23210 = unascribe t3  in
                          (uu____23210, imp)))
               in
            (uu____23105, uu____23114)
         in
      let rec aux qopt out t1 =
        let uu____23299 = let uu____23331 = flat t1  in (qopt, uu____23331)
           in
        match uu____23299 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____23387;
                 FStar_Syntax_Syntax.vars = uu____23388;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____23391);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____23392;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____23393;_},uu____23394)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____23582;
                 FStar_Syntax_Syntax.vars = uu____23583;_},uu____23584::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____23587);
                  FStar_Syntax_Syntax.pos = uu____23588;
                  FStar_Syntax_Syntax.vars = uu____23589;_},uu____23590)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____23801;
               FStar_Syntax_Syntax.vars = uu____23802;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____23805);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____23806;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____23807;_},uu____23808)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____23986 =
              let uu____23990 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____23990  in
            aux uu____23986 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____24009;
               FStar_Syntax_Syntax.vars = uu____24010;_},uu____24011::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____24014);
                FStar_Syntax_Syntax.pos = uu____24015;
                FStar_Syntax_Syntax.vars = uu____24016;_},uu____24017)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____24219 =
              let uu____24223 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____24223  in
            aux uu____24219 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____24242) ->
            let bs = FStar_List.rev out  in
            let uu____24321 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____24321 with
             | (bs1,t2) ->
                 let uu____24342 = patterns t2  in
                 (match uu____24342 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____24424 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let u_connectives =
      [(FStar_Parser_Const.true_lid, FStar_Parser_Const.c_true_lid,
         (Prims.parse_int "0"));
      (FStar_Parser_Const.false_lid, FStar_Parser_Const.c_false_lid,
        (Prims.parse_int "0"));
      (FStar_Parser_Const.and_lid, FStar_Parser_Const.c_and_lid,
        (Prims.parse_int "2"));
      (FStar_Parser_Const.or_lid, FStar_Parser_Const.c_or_lid,
        (Prims.parse_int "2"))]
       in
    let destruct_sq_base_conn t =
      let uu____24617 = un_squash t  in
      FStar_Util.bind_opt uu____24617
        (fun t1  ->
           let uu____24645 = head_and_args' t1  in
           match uu____24645 with
           | (hd1,args) ->
               let uu____24708 =
                 let uu____24714 =
                   let uu____24715 = un_uinst hd1  in
                   uu____24715.FStar_Syntax_Syntax.n  in
                 (uu____24714, (FStar_List.length args))  in
               (match uu____24708 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_24746) when
                    (_24746 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_24756) when
                    (_24756 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_24766) when
                    (_24766 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_24776) when
                    (_24776 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_24786) when
                    (_24786 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_24796) when
                    (_24796 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_24806) when
                    (_24806 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_24816) when
                    (_24816 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____24821 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____24863 = un_squash t  in
      FStar_Util.bind_opt uu____24863
        (fun t1  ->
           let uu____24890 = arrow_one t1  in
           match uu____24890 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____24921 =
                 let uu____24923 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____24923  in
               if uu____24921
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____24941 = comp_to_comp_typ_nouniv c  in
                    uu____24941.FStar_Syntax_Syntax.result_typ  in
                  let uu____24952 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____24952
                  then
                    let uu____24964 = patterns q  in
                    match uu____24964 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____25065 =
                       let uu____25066 =
                         let uu____25075 =
                           let uu____25076 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____25096 =
                             let uu____25111 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____25111]  in
                           uu____25076 :: uu____25096  in
                         (FStar_Parser_Const.imp_lid, uu____25075)  in
                       BaseConn uu____25066  in
                     FStar_Pervasives_Native.Some uu____25065))
           | uu____25164 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____25180 = un_squash t  in
      FStar_Util.bind_opt uu____25180
        (fun t1  ->
           let uu____25223 = head_and_args' t1  in
           match uu____25223 with
           | (hd1,args) ->
               let uu____25286 =
                 let uu____25305 =
                   let uu____25306 = un_uinst hd1  in
                   uu____25306.FStar_Syntax_Syntax.n  in
                 (uu____25305, args)  in
               (match uu____25286 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____25335)::(a2,uu____25337)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____25423 =
                      let uu____25424 = FStar_Syntax_Subst.compress a2  in
                      uu____25424.FStar_Syntax_Syntax.n  in
                    (match uu____25423 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____25439) ->
                         let uu____25516 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____25516 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____25616 -> failwith "impossible"  in
                              let uu____25629 = patterns q1  in
                              (match uu____25629 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____25728 -> FStar_Pervasives_Native.None)
                | uu____25729 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____25764 = destruct_sq_forall phi  in
          (match uu____25764 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _25782  -> FStar_Pervasives_Native.Some _25782)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____25798 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____25812 = destruct_sq_exists phi  in
          (match uu____25812 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _25830  -> FStar_Pervasives_Native.Some _25830)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____25846 -> f1)
      | uu____25849 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____25861 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____25861
      (fun uu____25866  ->
         let uu____25867 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____25867
           (fun uu____25872  ->
              let uu____25873 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____25873
                (fun uu____25878  ->
                   let uu____25879 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____25879
                     (fun uu____25884  ->
                        let uu____25885 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____25885
                          (fun uu____25889  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____25954 =
            let uu____25967 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____25967  in
          let uu____25982 =
            let uu____25991 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____25991  in
          let uu____26002 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____25954 a.FStar_Syntax_Syntax.action_univs uu____25982
            FStar_Parser_Const.effect_Tot_lid uu____26002 [] pos
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
          FStar_Syntax_Syntax.sigattrs = []
        }
  
let (mk_reify :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reify_1 =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
       in
    let uu____26107 =
      let uu____26114 =
        let uu____26115 =
          let uu____26140 =
            let uu____26155 = FStar_Syntax_Syntax.as_arg t  in [uu____26155]
             in
          (reify_1, uu____26140)  in
        FStar_Syntax_Syntax.Tm_app uu____26115  in
      FStar_Syntax_Syntax.mk uu____26114  in
    uu____26107 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____26247 =
        let uu____26254 =
          let uu____26255 =
            let uu____26256 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____26256  in
          FStar_Syntax_Syntax.Tm_constant uu____26255  in
        FStar_Syntax_Syntax.mk uu____26254  in
      uu____26247 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____26266 =
      let uu____26273 =
        let uu____26274 =
          let uu____26299 =
            let uu____26314 = FStar_Syntax_Syntax.as_arg t  in [uu____26314]
             in
          (reflect_, uu____26299)  in
        FStar_Syntax_Syntax.Tm_app uu____26274  in
      FStar_Syntax_Syntax.mk uu____26273  in
    uu____26266 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____26394 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____26431 = unfold_lazy i  in delta_qualifier uu____26431
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____26444 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____26450 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____26456 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____26494 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____26515 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____26516 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____26529 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____26530 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____26555) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____26568;
           FStar_Syntax_Syntax.index = uu____26569;
           FStar_Syntax_Syntax.sort = t2;_},uu____26571)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____26599) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____26613,uu____26614) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____26696) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____26737,t2,uu____26739) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____26796,t2) -> delta_qualifier t2
  
let rec (incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth) =
  fun d  ->
    match d with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Syntax_Syntax.Delta_constant_at_level
          (i + (Prims.parse_int "1"))
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Syntax_Syntax.Delta_equational_at_level
          (i + (Prims.parse_int "1"))
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
  
let (incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let uu____26865 = delta_qualifier t  in incr_delta_depth uu____26865
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26881 =
      let uu____26882 = FStar_Syntax_Subst.compress t  in
      uu____26882.FStar_Syntax_Syntax.n  in
    match uu____26881 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____26895 -> false
  
let rec apply_last :
  'Auu____26904 .
    ('Auu____26904 -> 'Auu____26904) ->
      'Auu____26904 Prims.list -> 'Auu____26904 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____26930 = f a  in [uu____26930]
      | x::xs -> let uu____26935 = apply_last f xs  in x :: uu____26935
  
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
  
let rec (mk_list :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term)
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____27074 =
            let uu____27081 =
              let uu____27082 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____27082  in
            FStar_Syntax_Syntax.mk uu____27081  in
          uu____27074 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____27106 =
            let uu____27111 =
              let uu____27120 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____27120
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____27111 args  in
          uu____27106 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____27146 =
            let uu____27151 =
              let uu____27160 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____27160
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____27151 args  in
          uu____27146 FStar_Pervasives_Native.None pos  in
        let uu____27169 =
          let uu____27178 =
            let uu____27179 = FStar_Syntax_Syntax.iarg typ  in [uu____27179]
             in
          nil uu____27178 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____27241 =
                 let uu____27242 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____27255 =
                   let uu____27270 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____27283 =
                     let uu____27298 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____27298]  in
                   uu____27270 :: uu____27283  in
                 uu____27242 :: uu____27255  in
               cons1 uu____27241 t.FStar_Syntax_Syntax.pos) l uu____27169
  
let rec eqlist :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq1  ->
    fun xs  ->
      fun ys  ->
        match (xs, ys) with
        | ([],[]) -> true
        | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
        | uu____27427 -> false
  
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
          | uu____27541 -> false
  
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
        | uu____27707 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____27745 = FStar_ST.op_Bang debug_term_eq  in
          if uu____27745
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
        let t11 = let uu____28083 = unmeta_safe t1  in canon_app uu____28083
           in
        let t21 = let uu____28105 = unmeta_safe t2  in canon_app uu____28105
           in
        let uu____28116 =
          let uu____28121 =
            let uu____28122 =
              let uu____28133 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____28133  in
            uu____28122.FStar_Syntax_Syntax.n  in
          let uu____28142 =
            let uu____28143 =
              let uu____28154 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____28154  in
            uu____28143.FStar_Syntax_Syntax.n  in
          (uu____28121, uu____28142)  in
        match uu____28116 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____28164,uu____28165) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____28178,FStar_Syntax_Syntax.Tm_uinst uu____28179) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____28192,uu____28193) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____28226,FStar_Syntax_Syntax.Tm_delayed uu____28227) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____28260,uu____28261) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____28310,FStar_Syntax_Syntax.Tm_ascribed uu____28311) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____28396 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____28396
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____28401 = FStar_Const.eq_const c1 c2  in
            check "const" uu____28401
        | (FStar_Syntax_Syntax.Tm_type
           uu____28404,FStar_Syntax_Syntax.Tm_type uu____28405) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____28527 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____28527) &&
              (let uu____28542 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____28542)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____28627 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____28627) &&
              (let uu____28642 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____28642)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____28696 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____28696)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____28785 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____28785) &&
              (let uu____28789 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____28789)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____28942 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____28942) &&
              (let uu____28946 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____28946)
        | (FStar_Syntax_Syntax.Tm_lazy uu____28974,uu____28975) ->
            let uu____28980 =
              let uu____28982 = unlazy t11  in
              term_eq_dbg dbg uu____28982 t21  in
            check "lazy_l" uu____28980
        | (uu____28992,FStar_Syntax_Syntax.Tm_lazy uu____28993) ->
            let uu____28998 =
              let uu____29000 = unlazy t21  in
              term_eq_dbg dbg t11 uu____29000  in
            check "lazy_r" uu____28998
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____29111 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____29111))
              &&
              (let uu____29122 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____29122)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____29126),FStar_Syntax_Syntax.Tm_uvar (u2,uu____29128)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____29248 =
               let uu____29250 = eq_quoteinfo qi1 qi2  in uu____29250 = Equal
                in
             check "tm_quoted qi" uu____29248) &&
              (let uu____29253 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____29253)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____29331 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____29331) &&
                   (let uu____29335 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____29335)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____29402 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____29402) &&
                    (let uu____29406 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____29406))
                   &&
                   (let uu____29410 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____29410)
             | uu____29413 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____29419) -> fail "unk"
        | (uu____29421,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____29423,uu____29424) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____29431,uu____29432) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____29439,uu____29440) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____29445,uu____29446) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____29448,uu____29449) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____29451,uu____29452) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____29488,uu____29489) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____29514,uu____29515) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____29532,uu____29533) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____29559,uu____29560) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____29599,uu____29600) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____29626,uu____29627) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____29649,uu____29650) ->
            fail "bottom"
        | (uu____29662,FStar_Syntax_Syntax.Tm_bvar uu____29663) ->
            fail "bottom"
        | (uu____29670,FStar_Syntax_Syntax.Tm_name uu____29671) ->
            fail "bottom"
        | (uu____29678,FStar_Syntax_Syntax.Tm_fvar uu____29679) ->
            fail "bottom"
        | (uu____29684,FStar_Syntax_Syntax.Tm_constant uu____29685) ->
            fail "bottom"
        | (uu____29687,FStar_Syntax_Syntax.Tm_type uu____29688) ->
            fail "bottom"
        | (uu____29690,FStar_Syntax_Syntax.Tm_abs uu____29691) ->
            fail "bottom"
        | (uu____29727,FStar_Syntax_Syntax.Tm_arrow uu____29728) ->
            fail "bottom"
        | (uu____29753,FStar_Syntax_Syntax.Tm_refine uu____29754) ->
            fail "bottom"
        | (uu____29771,FStar_Syntax_Syntax.Tm_app uu____29772) ->
            fail "bottom"
        | (uu____29798,FStar_Syntax_Syntax.Tm_match uu____29799) ->
            fail "bottom"
        | (uu____29838,FStar_Syntax_Syntax.Tm_let uu____29839) ->
            fail "bottom"
        | (uu____29865,FStar_Syntax_Syntax.Tm_uvar uu____29866) ->
            fail "bottom"
        | (uu____29888,FStar_Syntax_Syntax.Tm_meta uu____29889) ->
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
               let uu____29948 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____29948)
          (fun q1  ->
             fun q2  ->
               let uu____29960 =
                 let uu____29962 = eq_aqual q1 q2  in uu____29962 = Equal  in
               check "arg qual" uu____29960) a1 a2

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
               let uu____30012 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____30012)
          (fun q1  ->
             fun q2  ->
               let uu____30024 =
                 let uu____30026 = eq_aqual q1 q2  in uu____30026 = Equal  in
               check "binder qual" uu____30024) b1 b2

and (lcomp_eq_dbg :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c1  -> fun c2  -> fail "lcomp"

and (residual_eq_dbg :
  FStar_Syntax_Syntax.residual_comp ->
    FStar_Syntax_Syntax.residual_comp -> Prims.bool)
  = fun r1  -> fun r2  -> fail "residual"

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
        ((let uu____30104 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____30104) &&
           (let uu____30108 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____30108))
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
    fun uu____30118  ->
      fun uu____30119  ->
        match (uu____30118, uu____30119) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____30350 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____30350) &&
               (let uu____30354 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____30354))
              &&
              (let uu____30358 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____30448 -> false  in
               check "branch when" uu____30358)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____30491 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____30491) &&
           (let uu____30518 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____30518))
          &&
          (let uu____30522 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____30522)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____30555 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____30555 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____30617 ->
        let uu____30648 =
          let uu____30650 = FStar_Syntax_Subst.compress t  in
          sizeof uu____30650  in
        (Prims.parse_int "1") + uu____30648
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____30666 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____30666
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____30675 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____30675
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____30692 = sizeof t1  in (FStar_List.length us) + uu____30692
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____30696) ->
        let uu____30753 = sizeof t1  in
        let uu____30755 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____30775  ->
                 match uu____30775 with
                 | (bv,uu____30790) ->
                     let uu____30805 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____30805) (Prims.parse_int "0") bs
           in
        uu____30753 + uu____30755
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____30850 = sizeof hd1  in
        let uu____30852 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____30871  ->
                 match uu____30871 with
                 | (arg,uu____30885) ->
                     let uu____30898 = sizeof arg  in acc + uu____30898)
            (Prims.parse_int "0") args
           in
        uu____30850 + uu____30852
    | uu____30901 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____30931 =
        let uu____30932 = un_uinst t  in uu____30932.FStar_Syntax_Syntax.n
         in
      match uu____30931 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____30948 -> false
  
let (is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  -> is_fvar FStar_Parser_Const.synth_lid t 
let (has_attribute :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Ident.lident -> Prims.bool)
  = fun attrs  -> fun attr  -> FStar_Util.for_some (is_fvar attr) attrs 
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options1 t s =
        let uu____31025 = FStar_Options.set_options t s  in
        match uu____31025 with
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
      | FStar_Syntax_Syntax.LightOff  ->
          if p = FStar_Syntax_Syntax.LightOff
          then FStar_Options.set_ml_ish ()
          else ()
      | FStar_Syntax_Syntax.SetOptions o -> set_options1 FStar_Options.Set o
      | FStar_Syntax_Syntax.ResetOptions sopt ->
          ((let uu____31042 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____31042 (fun a1  -> ()));
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
      | FStar_Syntax_Syntax.PushOptions sopt ->
          (FStar_Options.internal_push ();
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
      | FStar_Syntax_Syntax.PopOptions  ->
          let uu____31057 = FStar_Options.internal_pop ()  in
          if uu____31057
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
    | FStar_Syntax_Syntax.Tm_delayed uu____31129 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____31179 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____31227 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____31236 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____31242 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____31273) ->
        let uu____31330 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____31330 with
         | (bs1,t2) ->
             let uu____31356 =
               FStar_List.collect
                 (fun uu____31383  ->
                    match uu____31383 with
                    | (b,uu____31403) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____31418 = unbound_variables t2  in
             FStar_List.append uu____31356 uu____31418)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____31471 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____31471 with
         | (bs1,c1) ->
             let uu____31497 =
               FStar_List.collect
                 (fun uu____31524  ->
                    match uu____31524 with
                    | (b,uu____31544) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____31559 = unbound_variables_comp c1  in
             FStar_List.append uu____31497 uu____31559)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____31596 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____31596 with
         | (bs,t2) ->
             let uu____31651 =
               FStar_List.collect
                 (fun uu____31678  ->
                    match uu____31678 with
                    | (b1,uu____31698) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____31713 = unbound_variables t2  in
             FStar_List.append uu____31651 uu____31713)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____31768 =
          FStar_List.collect
            (fun uu____31796  ->
               match uu____31796 with
               | (x,uu____31817) -> unbound_variables x) args
           in
        let uu____31834 = unbound_variables t1  in
        FStar_List.append uu____31768 uu____31834
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____31915 = unbound_variables t1  in
        let uu____31923 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____31953 = FStar_Syntax_Subst.open_branch br  in
                  match uu____31953 with
                  | (p,wopt,t2) ->
                      let uu____32002 = unbound_variables t2  in
                      let uu____32010 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____32002 uu____32010))
           in
        FStar_List.append uu____31915 uu____31923
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____32061) ->
        let uu____32142 = unbound_variables t1  in
        let uu____32150 =
          let uu____32158 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____32235 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____32158 uu____32235  in
        FStar_List.append uu____32142 uu____32150
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____32368 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____32376 =
          let uu____32384 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____32392 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____32407 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____32433 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____32433 with
                 | (uu____32478,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____32384 uu____32392  in
        FStar_List.append uu____32368 uu____32376
    | FStar_Syntax_Syntax.Tm_let ((uu____32498,lbs),t1) ->
        let uu____32547 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____32547 with
         | (lbs1,t2) ->
             let uu____32600 = unbound_variables t2  in
             let uu____32608 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____32639 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____32647 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____32639 uu____32647) lbs1
                in
             FStar_List.append uu____32600 uu____32608)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____32709 = unbound_variables t1  in
        let uu____32717 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____32732,args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____32821  ->
                      match uu____32821 with
                      | (a,uu____32842) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____32859,uu____32860,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____32890,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____32912 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____32926 -> []
          | FStar_Syntax_Syntax.Meta_named uu____32932 -> []  in
        FStar_List.append uu____32709 uu____32717

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____32962) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____32980) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____33003 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____33011 =
          FStar_List.collect
            (fun uu____33039  ->
               match uu____33039 with
               | (a,uu____33060) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____33003 uu____33011

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
            let uu____33268 = head_and_args h  in
            (match uu____33268 with
             | (head1,args) ->
                 let uu____33361 =
                   let uu____33362 = FStar_Syntax_Subst.compress head1  in
                   uu____33362.FStar_Syntax_Syntax.n  in
                 (match uu____33361 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____33458 -> aux (h :: acc) t))
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
      let uu____33518 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____33518 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2540_33600 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2540_33600.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2540_33600.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2540_33600.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2540_33600.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____33626 =
      let uu____33627 = FStar_Syntax_Subst.compress t  in
      uu____33627.FStar_Syntax_Syntax.n  in
    match uu____33626 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____33639,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____33690)::uu____33691 ->
                  let pats' = unmeta pats  in
                  let uu____33791 = head_and_args pats'  in
                  (match uu____33791 with
                   | (head1,uu____33818) ->
                       let uu____33859 =
                         let uu____33860 = un_uinst head1  in
                         uu____33860.FStar_Syntax_Syntax.n  in
                       (match uu____33859 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____33876 -> false))
              | uu____33878 -> false)
         | uu____33894 -> false)
    | uu____33896 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____33928 =
      let uu____33953 = unmeta e  in head_and_args uu____33953  in
    match uu____33928 with
    | (head1,args) ->
        let uu____34012 =
          let uu____34031 =
            let uu____34032 = un_uinst head1  in
            uu____34032.FStar_Syntax_Syntax.n  in
          (uu____34031, args)  in
        (match uu____34012 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____34066) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____34109::(hd1,uu____34111)::(tl1,uu____34113)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____34223 =
               let uu____34230 =
                 let uu____34237 = list_elements tl1  in
                 FStar_Util.must uu____34237  in
               hd1 :: uu____34230  in
             FStar_Pervasives_Native.Some uu____34223
         | uu____34262 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____34311 =
      let uu____34312 = FStar_Syntax_Subst.compress t  in
      uu____34312.FStar_Syntax_Syntax.n  in
    match uu____34311 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____34331) ->
        let uu____34408 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____34408 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____34478 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____34478
             then
               let uu____34494 =
                 let uu____34509 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____34509]  in
               mk_app t uu____34494
             else e1)
    | uu____34548 ->
        let uu____34549 =
          let uu____34564 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____34564]  in
        mk_app t uu____34549
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____34663 = list_elements e  in
        match uu____34663 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____34730 =
          let uu____34755 = unmeta p  in
          FStar_All.pipe_right uu____34755 head_and_args  in
        match uu____34730 with
        | (head1,args) ->
            let uu____34846 =
              let uu____34865 =
                let uu____34866 = un_uinst head1  in
                uu____34866.FStar_Syntax_Syntax.n  in
              (uu____34865, args)  in
            (match uu____34846 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____34904,uu____34905)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____34988 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____35079 =
            let uu____35104 = unmeta t1  in
            FStar_All.pipe_right uu____35104 head_and_args  in
          match uu____35079 with
          | (head1,args) ->
              let uu____35191 =
                let uu____35210 =
                  let uu____35211 = un_uinst head1  in
                  uu____35211.FStar_Syntax_Syntax.n  in
                (uu____35210, args)  in
              (match uu____35191 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____35246)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____35310 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____35364 = smt_pat_or1 t1  in
            (match uu____35364 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____35402 = list_elements1 e  in
                 FStar_All.pipe_right uu____35402
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____35456 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____35456
                           (FStar_List.map one_pat)))
             | uu____35499 ->
                 let uu____35508 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____35508])
        | uu____35587 ->
            let uu____35594 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____35594]
         in
      let uu____35673 =
        let uu____35723 =
          let uu____35724 = FStar_Syntax_Subst.compress t  in
          uu____35724.FStar_Syntax_Syntax.n  in
        match uu____35723 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____35824 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____35824 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____35941;
                        FStar_Syntax_Syntax.effect_name = uu____35942;
                        FStar_Syntax_Syntax.result_typ = uu____35943;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____35945)::(post,uu____35947)::(pats,uu____35949)::[];
                        FStar_Syntax_Syntax.flags = uu____35950;_}
                      ->
                      let uu____36059 = lemma_pats pats  in
                      (binders1, pre, post, uu____36059)
                  | uu____36117 -> failwith "impos"))
        | uu____36168 -> failwith "Impos"  in
      match uu____35673 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____36331 =
              let uu____36338 =
                let uu____36339 =
                  let uu____36350 = mk_imp pre post1  in
                  let uu____36361 =
                    let uu____36362 =
                      let uu____36391 =
                        FStar_Syntax_Syntax.binders_to_names binders  in
                      (uu____36391, patterns)  in
                    FStar_Syntax_Syntax.Meta_pattern uu____36362  in
                  (uu____36350, uu____36361)  in
                FStar_Syntax_Syntax.Tm_meta uu____36339  in
              FStar_Syntax_Syntax.mk uu____36338  in
            uu____36331 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____36439 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____36439 body
             in
          quant
  