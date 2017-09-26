open Prims
let qual_id: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun id1  ->
      let uu____9 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1]) in
      FStar_Ident.set_lid_range uu____9 id1.FStar_Ident.idRange
let mk_discriminator: FStar_Ident.lident -> FStar_Ident.lident =
  fun lid  ->
    FStar_Ident.lid_of_ids
      (FStar_List.append lid.FStar_Ident.ns
         [FStar_Ident.mk_ident
            ((Prims.strcat FStar_Ident.reserved_prefix
                (Prims.strcat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))])
let is_name: FStar_Ident.lident -> Prims.bool =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0") in
    FStar_Util.is_upper c
let arg_of_non_null_binder:
  'Auu____35 .
    (FStar_Syntax_Syntax.bv,'Auu____35) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term,'Auu____35) FStar_Pervasives_Native.tuple2
  =
  fun uu____47  ->
    match uu____47 with
    | (b,imp) ->
        let uu____54 = FStar_Syntax_Syntax.bv_to_name b in (uu____54, imp)
let args_of_non_null_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____78 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____78
            then []
            else (let uu____90 = arg_of_non_null_binder b in [uu____90])))
let args_of_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2
  =
  fun binders  ->
    let uu____115 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____161 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____161
              then
                let b1 =
                  let uu____179 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  (uu____179, (FStar_Pervasives_Native.snd b)) in
                let uu____180 = arg_of_non_null_binder b1 in (b1, uu____180)
              else
                (let uu____194 = arg_of_non_null_binder b in (b, uu____194)))) in
    FStar_All.pipe_right uu____115 FStar_List.unzip
let name_binders:
  FStar_Syntax_Syntax.binder Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____277 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____277
              then
                let uu____282 = b in
                match uu____282 with
                | (a,imp) ->
                    let b1 =
                      let uu____290 =
                        let uu____291 = FStar_Util.string_of_int i in
                        Prims.strcat "_" uu____291 in
                      FStar_Ident.id_of_text uu____290 in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      } in
                    (b2, imp)
              else b))
let name_function_binders:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____324 =
          let uu____327 =
            let uu____328 =
              let uu____341 = name_binders binders in (uu____341, comp) in
            FStar_Syntax_Syntax.Tm_arrow uu____328 in
          FStar_Syntax_Syntax.mk uu____327 in
        uu____324 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____359 -> t
let null_binders_of_tks:
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____400  ->
            match uu____400 with
            | (t,imp) ->
                let uu____411 =
                  let uu____412 = FStar_Syntax_Syntax.null_binder t in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____412 in
                (uu____411, imp)))
let binders_of_tks:
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____463  ->
            match uu____463 with
            | (t,imp) ->
                let uu____480 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t in
                (uu____480, imp)))
let binders_of_freevars:
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list
  =
  fun fvs  ->
    let uu____491 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____491
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
let mk_subst: 'Auu____502 . 'Auu____502 -> 'Auu____502 Prims.list =
  fun s  -> [s]
let subst_of_list:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.subst_t
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
let rename_binders:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t
  =
  fun replace_xs  ->
    fun with_ys  ->
      if (FStar_List.length replace_xs) = (FStar_List.length with_ys)
      then
        FStar_List.map2
          (fun uu____593  ->
             fun uu____594  ->
               match (uu____593, uu____594) with
               | ((x,uu____612),(y,uu____614)) ->
                   let uu____623 =
                     let uu____630 = FStar_Syntax_Syntax.bv_to_name y in
                     (x, uu____630) in
                   FStar_Syntax_Syntax.NT uu____623) replace_xs with_ys
      else failwith "Ill-formed substitution"
let rec unmeta: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____638) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____644,uu____645) -> unmeta e2
    | uu____686 -> e1
let rec unmeta_safe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____698 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____705 -> e1
         | uu____714 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____716,uu____717) ->
        unmeta_safe e2
    | uu____758 -> e1
let rec univ_kernel:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____771 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____772 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____782 = univ_kernel u1 in
        (match uu____782 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____793 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____800 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let constant_univ_as_nat: FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  ->
    let uu____809 = univ_kernel u in FStar_Pervasives_Native.snd uu____809
let rec compare_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____822,uu____823) ->
          failwith "Impossible: compare_univs"
      | (uu____824,FStar_Syntax_Syntax.U_bvar uu____825) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_unknown ,uu____826) -> - (Prims.parse_int "1")
      | (uu____827,FStar_Syntax_Syntax.U_unknown ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_zero ,uu____828) -> - (Prims.parse_int "1")
      | (uu____829,FStar_Syntax_Syntax.U_zero ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____832,FStar_Syntax_Syntax.U_unif
         uu____833) -> - (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____842,FStar_Syntax_Syntax.U_name
         uu____843) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____870 = FStar_Syntax_Unionfind.univ_uvar_id u11 in
          let uu____871 = FStar_Syntax_Unionfind.univ_uvar_id u21 in
          uu____870 - uu____871
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1 in
          let n2 = FStar_List.length us2 in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____902 = FStar_List.zip us1 us2 in
               FStar_Util.find_map uu____902
                 (fun uu____917  ->
                    match uu____917 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21 in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None) in
             match copt with
             | FStar_Pervasives_Native.None  -> Prims.parse_int "0"
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____931,uu____932) ->
          - (Prims.parse_int "1")
      | (uu____935,FStar_Syntax_Syntax.U_max uu____936) ->
          Prims.parse_int "1"
      | uu____939 ->
          let uu____944 = univ_kernel u1 in
          (match uu____944 with
           | (k1,n1) ->
               let uu____951 = univ_kernel u2 in
               (match uu____951 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2 in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
let eq_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____968 = compare_univs u1 u2 in
      uu____968 = (Prims.parse_int "0")
let ml_comp:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp
  =
  fun t  ->
    fun r  ->
      FStar_Syntax_Syntax.mk_Comp
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name =
            (FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }
let comp_effect_name:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____996 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1005 ->
        FStar_Parser_Const.effect_GTot_lid
let comp_flags:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1026 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1035 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
let comp_set_flags:
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    fun f  ->
      let comp_to_comp_typ c1 =
        match c1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Comp c2 -> c2
        | FStar_Syntax_Syntax.Total (t,u_opt) ->
            let uu____1074 =
              let uu____1075 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____1075 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____1074;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
        | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
            let uu____1102 =
              let uu____1103 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____1103 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____1102;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            } in
      let uu___169_1120 = c in
      let uu____1121 =
        let uu____1122 =
          let uu___170_1123 = comp_to_comp_typ c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___170_1123.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___170_1123.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___170_1123.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___170_1123.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu____1122 in
      {
        FStar_Syntax_Syntax.n = uu____1121;
        FStar_Syntax_Syntax.pos = (uu___169_1120.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___169_1120.FStar_Syntax_Syntax.vars)
      }
let comp_to_comp_typ:
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
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
    | uu____1157 ->
        failwith "Assertion failed: Computation type without universe"
let is_named_tot:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1167 -> true
    | FStar_Syntax_Syntax.GTotal uu____1176 -> false
let is_total_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___157_1196  ->
               match uu___157_1196 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1197 -> false)))
let is_total_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___158_1205  ->
               match uu___158_1205 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1206 -> false)))
let is_tot_or_gtot_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
        FStar_Parser_Const.effect_Tot_lid)
       ||
       (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
          FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___159_1214  ->
               match uu___159_1214 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1215 -> false)))
let is_partial_return:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___160_1227  ->
            match uu___160_1227 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1228 -> false))
let is_lcomp_partial_return: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___161_1236  ->
            match uu___161_1236 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1237 -> false))
let is_tot_or_gtot_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    (is_total_comp c) ||
      (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid
         (comp_effect_name c))
let is_pure_effect: FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)
let is_pure_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1258 -> true
    | FStar_Syntax_Syntax.GTotal uu____1267 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___162_1280  ->
                   match uu___162_1280 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1281 -> false)))
let is_ghost_effect: FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)
let is_pure_or_ghost_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  -> (is_pure_comp c) || (is_ghost_effect (comp_effect_name c))
let is_pure_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___163_1301  ->
               match uu___163_1301 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1302 -> false)))
let is_pure_or_ghost_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
let is_pure_or_ghost_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1311 =
      let uu____1312 = FStar_Syntax_Subst.compress t in
      uu____1312.FStar_Syntax_Syntax.n in
    match uu____1311 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1315,c) -> is_pure_or_ghost_comp c
    | uu____1333 -> true
let is_lemma_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1343 -> false
let is_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1348 =
      let uu____1349 = FStar_Syntax_Subst.compress t in
      uu____1349.FStar_Syntax_Syntax.n in
    match uu____1348 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1352,c) -> is_lemma_comp c
    | uu____1370 -> false
let head_and_args:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax,
                                                            FStar_Syntax_Syntax.aqual)
                                                            FStar_Pervasives_Native.tuple2
                                                            Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____1436 -> (t1, [])
let rec head_and_args':
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.term'
                                 FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1502 = head_and_args' head1 in
        (match uu____1502 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1559 -> (t1, [])
let un_uinst: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1580) ->
        FStar_Syntax_Subst.compress t2
    | uu____1585 -> t1
let is_smt_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1590 =
      let uu____1591 = FStar_Syntax_Subst.compress t in
      uu____1591.FStar_Syntax_Syntax.n in
    match uu____1590 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1594,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1616)::uu____1617 ->
                  let pats' = unmeta pats in
                  let uu____1661 = head_and_args pats' in
                  (match uu____1661 with
                   | (head1,uu____1677) ->
                       let uu____1698 =
                         let uu____1699 = un_uinst head1 in
                         uu____1699.FStar_Syntax_Syntax.n in
                       (match uu____1698 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1703 -> false))
              | uu____1704 -> false)
         | uu____1713 -> false)
    | uu____1714 -> false
let is_ml_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
           FStar_Parser_Const.effect_ML_lid)
          ||
          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___164_1727  ->
                   match uu___164_1727 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1728 -> false)))
    | uu____1729 -> false
let comp_result:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1743) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1753) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let set_result_typ:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____1775 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____1784 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___171_1796 = ct in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___171_1796.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___171_1796.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___171_1796.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___171_1796.FStar_Syntax_Syntax.flags)
             })
let is_trivial_wp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___165_1808  ->
            match uu___165_1808 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____1809 -> false))
let primops: FStar_Ident.lident Prims.list =
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
let is_primop_lid: FStar_Ident.lident -> Prims.bool =
  fun l  ->
    FStar_All.pipe_right primops
      (FStar_Util.for_some (FStar_Ident.lid_equals l))
let is_primop:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_primop_lid (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____1827 -> false
let rec unascribe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1834,uu____1835) ->
        unascribe e2
    | uu____1876 -> e1
let rec ascribe:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.comp'
                                                             FStar_Syntax_Syntax.syntax)
       FStar_Util.either,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun k  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1926,uu____1927) ->
          ascribe t' k
      | uu____1968 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
type eq_result =
  | Equal
  | NotEqual
  | Unknown[@@deriving show]
let uu___is_Equal: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1993 -> false
let uu___is_NotEqual: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1998 -> false
let uu___is_Unknown: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2003 -> false
let rec eq_tm:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        let uu____2024 =
          let uu____2037 = unascribe t in head_and_args' uu____2037 in
        match uu____2024 with
        | (hd1,args) ->
            FStar_Syntax_Syntax.mk_Tm_app hd1 args
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
      let equal_if uu___166_2067 = if uu___166_2067 then Equal else Unknown in
      let equal_iff uu___167_2072 = if uu___167_2072 then Equal else NotEqual in
      let eq_and f g = match f with | Equal  -> g () | uu____2086 -> Unknown in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2094) -> NotEqual
        | (uu____2095,NotEqual ) -> NotEqual
        | (Unknown ,uu____2096) -> Unknown
        | (uu____2097,Unknown ) -> Unknown in
      let equal_data f1 args1 f2 args2 =
        let uu____2135 = FStar_Syntax_Syntax.fv_eq f1 f2 in
        if uu____2135
        then
          let uu____2139 = FStar_List.zip args1 args2 in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2197  ->
                    match uu____2197 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2225 = eq_tm a1 a2 in eq_inj acc uu____2225)
               Equal) uu____2139
        else NotEqual in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          if
            (f.FStar_Syntax_Syntax.fv_qual =
               (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
              &&
              (g.FStar_Syntax_Syntax.fv_qual =
                 (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
          then equal_data f [] g []
          else
            (let uu____2244 = FStar_Syntax_Syntax.fv_eq f g in
             equal_if uu____2244)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2257 = eq_tm f g in
          eq_and uu____2257
            (fun uu____2260  ->
               let uu____2261 = eq_univs_list us vs in equal_if uu____2261)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2264 = FStar_Const.eq_const c d in equal_iff uu____2264
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2266),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2268)) ->
          let uu____2317 = FStar_Syntax_Unionfind.equiv u1 u2 in
          equal_if uu____2317
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2362 =
            let uu____2367 =
              let uu____2368 = un_uinst h1 in
              uu____2368.FStar_Syntax_Syntax.n in
            let uu____2371 =
              let uu____2372 = un_uinst h2 in
              uu____2372.FStar_Syntax_Syntax.n in
            (uu____2367, uu____2371) in
          (match uu____2362 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (f1.FStar_Syntax_Syntax.fv_qual =
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
                 &&
                 (f2.FStar_Syntax_Syntax.fv_qual =
                    (FStar_Pervasives_Native.Some
                       FStar_Syntax_Syntax.Data_ctor))
               -> equal_data f1 args1 f2 args2
           | uu____2381 ->
               let uu____2386 = eq_tm h1 h2 in
               eq_and uu____2386 (fun uu____2388  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____2391 = eq_univs u v1 in equal_if uu____2391
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____2393),uu____2394) ->
          eq_tm t12 t21
      | (uu____2399,FStar_Syntax_Syntax.Tm_meta (t22,uu____2401)) ->
          eq_tm t11 t22
      | uu____2406 -> Unknown
and eq_args:
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____2442)::a11,(b,uu____2445)::b1) ->
          let uu____2499 = eq_tm a b in
          (match uu____2499 with
           | Equal  -> eq_args a11 b1
           | uu____2500 -> Unknown)
      | uu____2501 -> Unknown
and eq_univs_list:
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool
  =
  fun us  ->
    fun vs  ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)
let rec unrefine: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____2514) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2520,uu____2521) ->
        unrefine t2
    | uu____2562 -> t1
let rec is_unit: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2567 =
      let uu____2568 = unrefine t in uu____2568.FStar_Syntax_Syntax.n in
    match uu____2567 with
    | FStar_Syntax_Syntax.Tm_type uu____2571 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2574) -> is_unit t1
    | uu____2579 -> false
let rec non_informative: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2584 =
      let uu____2585 = unrefine t in uu____2585.FStar_Syntax_Syntax.n in
    match uu____2584 with
    | FStar_Syntax_Syntax.Tm_type uu____2588 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____2591) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2613) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____2618,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____2636 -> false
let is_fun: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____2641 =
      let uu____2642 = FStar_Syntax_Subst.compress e in
      uu____2642.FStar_Syntax_Syntax.n in
    match uu____2641 with
    | FStar_Syntax_Syntax.Tm_abs uu____2645 -> true
    | uu____2662 -> false
let is_function_typ: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2667 =
      let uu____2668 = FStar_Syntax_Subst.compress t in
      uu____2668.FStar_Syntax_Syntax.n in
    match uu____2667 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2671 -> true
    | uu____2684 -> false
let rec pre_typ: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____2691) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2697,uu____2698) ->
        pre_typ t2
    | uu____2739 -> t1
let destruct:
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ in
      let uu____2759 =
        let uu____2760 = un_uinst typ1 in uu____2760.FStar_Syntax_Syntax.n in
      match uu____2759 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1 in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____2815 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____2839 -> FStar_Pervasives_Native.None
let lids_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____2856,lids) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____2862,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2873,uu____2874,uu____2875,uu____2876,uu____2877) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____2887,uu____2888,uu____2889,uu____2890) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____2896,uu____2897,uu____2898,uu____2899,uu____2900) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2906,uu____2907) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2909,uu____2910) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____2913 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____2914 -> []
    | FStar_Syntax_Syntax.Sig_main uu____2915 -> []
let lid_of_sigelt:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____2927 -> FStar_Pervasives_Native.None
let quals_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals
let range_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng
let range_of_lb:
  'Auu____2946 'Auu____2947 .
    ((FStar_Syntax_Syntax.bv,FStar_Ident.lid) FStar_Util.either,'Auu____2947,
      'Auu____2946) FStar_Pervasives_Native.tuple3 -> FStar_Range.range
  =
  fun uu___168_2961  ->
    match uu___168_2961 with
    | (FStar_Util.Inl x,uu____2973,uu____2974) ->
        FStar_Syntax_Syntax.range_of_bv x
    | (FStar_Util.Inr l,uu____2980,uu____2981) -> FStar_Ident.range_of_lid l
let range_of_arg:
  'Auu____2992 'Auu____2993 .
    ('Auu____2993 FStar_Syntax_Syntax.syntax,'Auu____2992)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____3003  ->
    match uu____3003 with | (hd1,uu____3011) -> hd1.FStar_Syntax_Syntax.pos
let range_of_args:
  'Auu____3024 'Auu____3025 .
    ('Auu____3025 FStar_Syntax_Syntax.syntax,'Auu____3024)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range -> FStar_Range.range
  =
  fun args  ->
    fun r  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left
           (fun r1  -> fun a  -> FStar_Range.union_ranges r1 (range_of_arg a))
           r)
let mk_app:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun f  ->
    fun args  ->
      let r = range_of_args args f.FStar_Syntax_Syntax.pos in
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args))
        FStar_Pervasives_Native.None r
let mk_data:
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun l  ->
    fun args  ->
      match args with
      | [] ->
          let uu____3149 =
            let uu____3152 =
              let uu____3153 =
                let uu____3160 =
                  FStar_Syntax_Syntax.fvar l
                    FStar_Syntax_Syntax.Delta_constant
                    (FStar_Pervasives_Native.Some
                       FStar_Syntax_Syntax.Data_ctor) in
                (uu____3160,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Data_app)) in
              FStar_Syntax_Syntax.Tm_meta uu____3153 in
            FStar_Syntax_Syntax.mk uu____3152 in
          uu____3149 FStar_Pervasives_Native.None
            (FStar_Ident.range_of_lid l)
      | uu____3164 ->
          let e =
            let uu____3176 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            mk_app uu____3176 args in
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_meta
               (e,
                 (FStar_Syntax_Syntax.Meta_desugared
                    FStar_Syntax_Syntax.Data_app)))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
let mangle_field_name: FStar_Ident.ident -> FStar_Ident.ident =
  fun x  ->
    FStar_Ident.mk_ident
      ((Prims.strcat "__fname__" x.FStar_Ident.idText),
        (x.FStar_Ident.idRange))
let unmangle_field_name: FStar_Ident.ident -> FStar_Ident.ident =
  fun x  ->
    if FStar_Util.starts_with x.FStar_Ident.idText "__fname__"
    then
      let uu____3189 =
        let uu____3194 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9") in
        (uu____3194, (x.FStar_Ident.idRange)) in
      FStar_Ident.mk_ident uu____3189
    else x
let field_projector_prefix: Prims.string = "__proj__"
let field_projector_sep: Prims.string = "__item__"
let field_projector_contains_constructor: Prims.string -> Prims.bool =
  fun s  -> FStar_Util.starts_with s field_projector_prefix
let mk_field_projector_name_from_string:
  Prims.string -> Prims.string -> Prims.string =
  fun constr  ->
    fun field  ->
      Prims.strcat field_projector_prefix
        (Prims.strcat constr (Prims.strcat field_projector_sep field))
let mk_field_projector_name_from_ident:
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun i  ->
      let j = unmangle_field_name i in
      let jtext = j.FStar_Ident.idText in
      let newi =
        if field_projector_contains_constructor jtext
        then j
        else
          FStar_Ident.mk_ident
            ((mk_field_projector_name_from_string
                (lid.FStar_Ident.ident).FStar_Ident.idText jtext),
              (i.FStar_Ident.idRange)) in
      FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns [newi])
let mk_field_projector_name:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv ->
      Prims.int ->
        (FStar_Ident.lident,FStar_Syntax_Syntax.bv)
          FStar_Pervasives_Native.tuple2
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____3237 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____3237
          then
            let uu____3238 =
              let uu____3243 =
                let uu____3244 = FStar_Util.string_of_int i in
                Prims.strcat "_" uu____3244 in
              let uu____3245 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____3243, uu____3245) in
            FStar_Ident.mk_ident uu____3238
          else x.FStar_Syntax_Syntax.ppname in
        let y =
          let uu___172_3248 = x in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___172_3248.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___172_3248.FStar_Syntax_Syntax.sort)
          } in
        let uu____3249 = mk_field_projector_name_from_ident lid nm in
        (uu____3249, y)
let set_uvar:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun uv  ->
    fun t  ->
      let uu____3258 = FStar_Syntax_Unionfind.find uv in
      match uu____3258 with
      | FStar_Pervasives_Native.Some uu____3261 ->
          let uu____3262 =
            let uu____3263 =
              let uu____3264 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu____3264 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3263 in
          failwith uu____3262
      | uu____3265 -> FStar_Syntax_Unionfind.change uv t
let qualifier_equal:
  FStar_Syntax_Syntax.qualifier ->
    FStar_Syntax_Syntax.qualifier -> Prims.bool
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
      | uu____3338 -> q1 = q2
let abs:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        let close_lopt lopt1 =
          match lopt1 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rc ->
              let uu____3372 =
                let uu___173_3373 = rc in
                let uu____3374 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs) in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___173_3373.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____3374;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___173_3373.FStar_Syntax_Syntax.residual_flags)
                } in
              FStar_Pervasives_Native.Some uu____3372 in
        match bs with
        | [] -> t
        | uu____3385 ->
            let body =
              let uu____3387 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____3387 in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____3415 =
                   let uu____3418 =
                     let uu____3419 =
                       let uu____3436 =
                         let uu____3443 = FStar_Syntax_Subst.close_binders bs in
                         FStar_List.append uu____3443 bs' in
                       let uu____3454 = close_lopt lopt' in
                       (uu____3436, t1, uu____3454) in
                     FStar_Syntax_Syntax.Tm_abs uu____3419 in
                   FStar_Syntax_Syntax.mk uu____3418 in
                 uu____3415 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____3470 ->
                 let uu____3477 =
                   let uu____3480 =
                     let uu____3481 =
                       let uu____3498 = FStar_Syntax_Subst.close_binders bs in
                       let uu____3499 = close_lopt lopt in
                       (uu____3498, body, uu____3499) in
                     FStar_Syntax_Syntax.Tm_abs uu____3481 in
                   FStar_Syntax_Syntax.mk uu____3480 in
                 uu____3477 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos)
let arrow:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____3539 ->
          let uu____3546 =
            let uu____3549 =
              let uu____3550 =
                let uu____3563 = FStar_Syntax_Subst.close_binders bs in
                let uu____3564 = FStar_Syntax_Subst.close_comp bs c in
                (uu____3563, uu____3564) in
              FStar_Syntax_Syntax.Tm_arrow uu____3550 in
            FStar_Syntax_Syntax.mk uu____3549 in
          uu____3546 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
let flat_arrow:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c in
      let uu____3597 =
        let uu____3598 = FStar_Syntax_Subst.compress t in
        uu____3598.FStar_Syntax_Syntax.n in
      match uu____3597 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____3624) ->
               let uu____3633 =
                 let uu____3634 = FStar_Syntax_Subst.compress tres in
                 uu____3634.FStar_Syntax_Syntax.n in
               (match uu____3633 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____3669 -> t)
           | uu____3670 -> t)
      | uu____3671 -> t
let refine:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____3682 =
        let uu____3683 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____3683 t.FStar_Syntax_Syntax.pos in
      let uu____3684 =
        let uu____3687 =
          let uu____3688 =
            let uu____3695 =
              let uu____3696 =
                let uu____3697 = FStar_Syntax_Syntax.mk_binder b in
                [uu____3697] in
              FStar_Syntax_Subst.close uu____3696 t in
            (b, uu____3695) in
          FStar_Syntax_Syntax.Tm_refine uu____3688 in
        FStar_Syntax_Syntax.mk uu____3687 in
      uu____3684 FStar_Pervasives_Native.None uu____3682
let branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun b  -> FStar_Syntax_Subst.close_branch b
let rec arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____3748 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____3748 with
         | (bs1,c1) ->
             let uu____3765 = is_tot_or_gtot_comp c1 in
             if uu____3765
             then
               let uu____3776 = arrow_formals_comp (comp_result c1) in
               (match uu____3776 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____3822 ->
        let uu____3823 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3823)
let rec arrow_formals:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let uu____3850 = arrow_formals_comp k in
    match uu____3850 with | (bs,c) -> (bs, (comp_result c))
let abs_formals:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.residual_comp
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____3927 =
            let uu___174_3928 = rc in
            let uu____3929 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___174_3928.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____3929;
              FStar_Syntax_Syntax.residual_flags =
                (uu___174_3928.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____3927
      | uu____3936 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____3964 =
        let uu____3965 =
          let uu____3968 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____3968 in
        uu____3965.FStar_Syntax_Syntax.n in
      match uu____3964 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____4006 = aux t2 what in
          (match uu____4006 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____4066 -> ([], t1, abs_body_lcomp) in
    let uu____4079 = aux t FStar_Pervasives_Native.None in
    match uu____4079 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____4121 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____4121 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp in
             (bs1, t2, abs_body_lcomp1))
let mk_letbinding:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.letbinding
  =
  fun lbname  ->
    fun univ_vars  ->
      fun typ  ->
        fun eff  ->
          fun def  ->
            {
              FStar_Syntax_Syntax.lbname = lbname;
              FStar_Syntax_Syntax.lbunivs = univ_vars;
              FStar_Syntax_Syntax.lbtyp = typ;
              FStar_Syntax_Syntax.lbeff = eff;
              FStar_Syntax_Syntax.lbdef = def
            }
let close_univs_and_mk_letbinding:
  FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Ident.ident Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.letbinding
  =
  fun recs  ->
    fun lbname  ->
      fun univ_vars  ->
        fun typ  ->
          fun eff  ->
            fun def  ->
              let def1 =
                match (recs, univ_vars) with
                | (FStar_Pervasives_Native.None ,uu____4235) -> def
                | (uu____4246,[]) -> def
                | (FStar_Pervasives_Native.Some fvs,uu____4258) ->
                    let universes =
                      FStar_All.pipe_right univ_vars
                        (FStar_List.map
                           (fun _0_28  -> FStar_Syntax_Syntax.U_name _0_28)) in
                    let inst1 =
                      FStar_All.pipe_right fvs
                        (FStar_List.map
                           (fun fv  ->
                              (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                universes))) in
                    FStar_Syntax_InstFV.instantiate inst1 def in
              let typ1 = FStar_Syntax_Subst.close_univ_vars univ_vars typ in
              let def2 = FStar_Syntax_Subst.close_univ_vars univ_vars def1 in
              mk_letbinding lbname univ_vars typ1 eff def2
let open_univ_vars_binders_and_comp:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                          FStar_Pervasives_Native.tuple2
                                          Prims.list,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple3
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____4361 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____4361 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____4390 ->
            let t' = arrow binders c in
            let uu____4400 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____4400 with
             | (uvs1,t'1) ->
                 let uu____4419 =
                   let uu____4420 = FStar_Syntax_Subst.compress t'1 in
                   uu____4420.FStar_Syntax_Syntax.n in
                 (match uu____4419 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____4461 -> failwith "Impossible"))
let is_tuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____4479 -> false
let is_dtuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____4485 -> false
let is_lid_equality: FStar_Ident.lident -> Prims.bool =
  fun x  -> FStar_Ident.lid_equals x FStar_Parser_Const.eq2_lid
let is_forall: FStar_Ident.lident -> Prims.bool =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.forall_lid
let is_exists: FStar_Ident.lident -> Prims.bool =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.exists_lid
let is_qlid: FStar_Ident.lident -> Prims.bool =
  fun lid  -> (is_forall lid) || (is_exists lid)
let is_equality:
  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.bool =
  fun x  -> is_lid_equality x.FStar_Syntax_Syntax.v
let lid_is_connective: FStar_Ident.lident -> Prims.bool =
  let lst =
    [FStar_Parser_Const.and_lid;
    FStar_Parser_Const.or_lid;
    FStar_Parser_Const.not_lid;
    FStar_Parser_Const.iff_lid;
    FStar_Parser_Const.imp_lid] in
  fun lid  -> FStar_Util.for_some (FStar_Ident.lid_equals lid) lst
let is_constructor:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____4525 =
        let uu____4526 = pre_typ t in uu____4526.FStar_Syntax_Syntax.n in
      match uu____4525 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____4530 -> false
let rec is_constructed_typ:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____4539 =
        let uu____4540 = pre_typ t in uu____4540.FStar_Syntax_Syntax.n in
      match uu____4539 with
      | FStar_Syntax_Syntax.Tm_fvar uu____4543 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____4545) ->
          is_constructed_typ t1 lid
      | uu____4566 -> false
let rec get_tycon:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____4576 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____4577 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____4578 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____4580) -> get_tycon t2
    | uu____4601 -> FStar_Pervasives_Native.None
let is_interpreted: FStar_Ident.lident -> Prims.bool =
  fun l  ->
    let theory_syms =
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
      FStar_Parser_Const.op_Negation] in
    FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4613 =
      let uu____4614 = un_uinst t in uu____4614.FStar_Syntax_Syntax.n in
    match uu____4613 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Parser_Const.fstar_refl_embed_lid
    | uu____4618 -> false
let is_fstar_tactics_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4623 =
      let uu____4624 = un_uinst t in uu____4624.FStar_Syntax_Syntax.n in
    match uu____4623 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____4628 -> false
let ktype: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
let ktype0: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
let type_u:
  Prims.unit ->
    (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____4640  ->
    let u =
      let uu____4646 = FStar_Syntax_Unionfind.univ_fresh () in
      FStar_All.pipe_left (fun _0_29  -> FStar_Syntax_Syntax.U_unif _0_29)
        uu____4646 in
    let uu____4663 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange in
    (uu____4663, u)
let attr_substitute: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  let uu____4670 =
    let uu____4673 =
      let uu____4674 =
        let uu____4675 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange in
        FStar_Syntax_Syntax.lid_as_fv uu____4675
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
      FStar_Syntax_Syntax.Tm_fvar uu____4674 in
    FStar_Syntax_Syntax.mk uu____4673 in
  uu____4670 FStar_Pervasives_Native.None FStar_Range.dummyRange
let exp_true_bool: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
let exp_false_bool: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
let exp_unit: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
let exp_int: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_int (s, FStar_Pervasives_Native.None)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
let exp_string: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (s, FStar_Range.dummyRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
let fvar_const: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
      FStar_Pervasives_Native.None
let tand: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.and_lid
let tor: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.or_lid
let timp: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
let tiff: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    FStar_Pervasives_Native.None
let t_bool: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.bool_lid
let t_false: FStar_Syntax_Syntax.term =
  fvar_const FStar_Parser_Const.false_lid
let t_true: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.true_lid
let b2t_v: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.b2t_lid
let t_not: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.not_lid
let mk_conj_opt:
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu____4724 =
            let uu____4727 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            let uu____4728 =
              let uu____4731 =
                let uu____4732 =
                  let uu____4747 =
                    let uu____4750 = FStar_Syntax_Syntax.as_arg phi11 in
                    let uu____4751 =
                      let uu____4754 = FStar_Syntax_Syntax.as_arg phi2 in
                      [uu____4754] in
                    uu____4750 :: uu____4751 in
                  (tand, uu____4747) in
                FStar_Syntax_Syntax.Tm_app uu____4732 in
              FStar_Syntax_Syntax.mk uu____4731 in
            uu____4728 FStar_Pervasives_Native.None uu____4727 in
          FStar_Pervasives_Native.Some uu____4724
let mk_binop:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____4780 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos in
        let uu____4781 =
          let uu____4784 =
            let uu____4785 =
              let uu____4800 =
                let uu____4803 = FStar_Syntax_Syntax.as_arg phi1 in
                let uu____4804 =
                  let uu____4807 = FStar_Syntax_Syntax.as_arg phi2 in
                  [uu____4807] in
                uu____4803 :: uu____4804 in
              (op_t, uu____4800) in
            FStar_Syntax_Syntax.Tm_app uu____4785 in
          FStar_Syntax_Syntax.mk uu____4784 in
        uu____4781 FStar_Pervasives_Native.None uu____4780
let mk_neg:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun phi  ->
    let uu____4821 =
      let uu____4824 =
        let uu____4825 =
          let uu____4840 =
            let uu____4843 = FStar_Syntax_Syntax.as_arg phi in [uu____4843] in
          (t_not, uu____4840) in
        FStar_Syntax_Syntax.Tm_app uu____4825 in
      FStar_Syntax_Syntax.mk uu____4824 in
    uu____4821 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
let mk_conj:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun phi1  -> fun phi2  -> mk_binop tand phi1 phi2
let mk_conj_l:
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
let mk_disj:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun phi1  -> fun phi2  -> mk_binop tor phi1 phi2
let mk_disj_l:
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
let mk_imp:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun phi1  -> fun phi2  -> mk_binop timp phi1 phi2
let mk_iff:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun phi1  -> fun phi2  -> mk_binop tiff phi1 phi2
let b2t:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun e  ->
    let uu____4915 =
      let uu____4918 =
        let uu____4919 =
          let uu____4934 =
            let uu____4937 = FStar_Syntax_Syntax.as_arg e in [uu____4937] in
          (b2t_v, uu____4934) in
        FStar_Syntax_Syntax.Tm_app uu____4919 in
      FStar_Syntax_Syntax.mk uu____4918 in
    uu____4915 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
let teq: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.eq2_lid
let mk_untyped_eq2:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun e1  ->
    fun e2  ->
      let uu____4953 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos in
      let uu____4954 =
        let uu____4957 =
          let uu____4958 =
            let uu____4973 =
              let uu____4976 = FStar_Syntax_Syntax.as_arg e1 in
              let uu____4977 =
                let uu____4980 = FStar_Syntax_Syntax.as_arg e2 in
                [uu____4980] in
              uu____4976 :: uu____4977 in
            (teq, uu____4973) in
          FStar_Syntax_Syntax.Tm_app uu____4958 in
        FStar_Syntax_Syntax.mk uu____4957 in
      uu____4954 FStar_Pervasives_Native.None uu____4953
let mk_eq2:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun u  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          let eq_inst = FStar_Syntax_Syntax.mk_Tm_uinst teq [u] in
          let uu____5003 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          let uu____5004 =
            let uu____5007 =
              let uu____5008 =
                let uu____5023 =
                  let uu____5026 = FStar_Syntax_Syntax.iarg t in
                  let uu____5027 =
                    let uu____5030 = FStar_Syntax_Syntax.as_arg e1 in
                    let uu____5031 =
                      let uu____5034 = FStar_Syntax_Syntax.as_arg e2 in
                      [uu____5034] in
                    uu____5030 :: uu____5031 in
                  uu____5026 :: uu____5027 in
                (eq_inst, uu____5023) in
              FStar_Syntax_Syntax.Tm_app uu____5008 in
            FStar_Syntax_Syntax.mk uu____5007 in
          uu____5004 FStar_Pervasives_Native.None uu____5003
let mk_has_type:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      fun t'  ->
        let t_has_type = fvar_const FStar_Parser_Const.has_type_lid in
        let t_has_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst
               (t_has_type,
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]))
            FStar_Pervasives_Native.None FStar_Range.dummyRange in
        let uu____5060 =
          let uu____5063 =
            let uu____5064 =
              let uu____5079 =
                let uu____5082 = FStar_Syntax_Syntax.iarg t in
                let uu____5083 =
                  let uu____5086 = FStar_Syntax_Syntax.as_arg x in
                  let uu____5087 =
                    let uu____5090 = FStar_Syntax_Syntax.as_arg t' in
                    [uu____5090] in
                  uu____5086 :: uu____5087 in
                uu____5082 :: uu____5083 in
              (t_has_type1, uu____5079) in
            FStar_Syntax_Syntax.Tm_app uu____5064 in
          FStar_Syntax_Syntax.mk uu____5063 in
        uu____5060 FStar_Pervasives_Native.None FStar_Range.dummyRange
let lex_t: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.lex_t_lid
let lex_top: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  let uu____5100 =
    let uu____5103 =
      let uu____5104 =
        let uu____5111 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
        (uu____5111, [FStar_Syntax_Syntax.U_zero]) in
      FStar_Syntax_Syntax.Tm_uinst uu____5104 in
    FStar_Syntax_Syntax.mk uu____5103 in
  uu____5100 FStar_Pervasives_Native.None FStar_Range.dummyRange
let lex_pair: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let tforall: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
let t_haseq: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
let lcomp_of_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.lcomp
  =
  fun c0  ->
    let uu____5125 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____5138 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____5149 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags)) in
    match uu____5125 with
    | (eff_name,flags) ->
        {
          FStar_Syntax_Syntax.eff_name = eff_name;
          FStar_Syntax_Syntax.res_typ = (comp_result c0);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = ((fun uu____5170  -> c0))
        }
let mk_residual_comp:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.cflags Prims.list ->
        FStar_Syntax_Syntax.residual_comp
  =
  fun l  ->
    fun t  ->
      fun f  ->
        {
          FStar_Syntax_Syntax.residual_effect = l;
          FStar_Syntax_Syntax.residual_typ = t;
          FStar_Syntax_Syntax.residual_flags = f
        }
let residual_tot:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.residual_comp
  =
  fun t  ->
    {
      FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid;
      FStar_Syntax_Syntax.residual_typ = (FStar_Pervasives_Native.Some t);
      FStar_Syntax_Syntax.residual_flags = [FStar_Syntax_Syntax.TOTAL]
    }
let residual_comp_of_comp:
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.residual_comp =
  fun c  ->
    {
      FStar_Syntax_Syntax.residual_effect = (comp_effect_name c);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (comp_result c));
      FStar_Syntax_Syntax.residual_flags = (comp_flags c)
    }
let residual_comp_of_lcomp:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.residual_comp =
  fun lc  ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.FStar_Syntax_Syntax.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.FStar_Syntax_Syntax.cflags)
    }
let mk_forall_aux:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun fa  ->
    fun x  ->
      fun body  ->
        let uu____5235 =
          let uu____5238 =
            let uu____5239 =
              let uu____5254 =
                let uu____5257 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
                let uu____5258 =
                  let uu____5261 =
                    let uu____5262 =
                      let uu____5263 =
                        let uu____5264 = FStar_Syntax_Syntax.mk_binder x in
                        [uu____5264] in
                      abs uu____5263 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0)) in
                    FStar_Syntax_Syntax.as_arg uu____5262 in
                  [uu____5261] in
                uu____5257 :: uu____5258 in
              (fa, uu____5254) in
            FStar_Syntax_Syntax.Tm_app uu____5239 in
          FStar_Syntax_Syntax.mk uu____5238 in
        uu____5235 FStar_Pervasives_Native.None FStar_Range.dummyRange
let mk_forall_no_univ:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  = fun x  -> fun body  -> mk_forall_aux tforall x body
let mk_forall:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun u  ->
    fun x  ->
      fun body  ->
        let tforall1 = FStar_Syntax_Syntax.mk_Tm_uinst tforall [u] in
        mk_forall_aux tforall1 x body
let close_forall_no_univs:
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____5310 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____5310
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
let rec is_wild_pat:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____5320 -> true
    | uu____5321 -> false
let if_then_else:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t1  ->
      fun t2  ->
        let then_branch =
          let uu____5363 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos in
          (uu____5363, FStar_Pervasives_Native.None, t1) in
        let else_branch =
          let uu____5391 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos in
          (uu____5391, FStar_Pervasives_Native.None, t2) in
        let uu____5404 =
          let uu____5405 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____5405 in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____5404
let mk_squash:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun p  ->
    let sq =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
        (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
        FStar_Pervasives_Native.None in
    let uu____5473 =
      FStar_Syntax_Syntax.mk_Tm_uinst sq [FStar_Syntax_Syntax.U_zero] in
    let uu____5476 =
      let uu____5485 = FStar_Syntax_Syntax.as_arg p in [uu____5485] in
    mk_app uu____5473 uu____5476
let un_squash:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____5494 = head_and_args t in
    match uu____5494 with
    | (head1,args) ->
        let uu____5535 =
          let uu____5548 =
            let uu____5549 = un_uinst head1 in
            uu____5549.FStar_Syntax_Syntax.n in
          (uu____5548, args) in
        (match uu____5535 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____5566)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____5618 =
                    let uu____5623 =
                      let uu____5624 = FStar_Syntax_Syntax.mk_binder b in
                      [uu____5624] in
                    FStar_Syntax_Subst.open_term uu____5623 p in
                  (match uu____5618 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____5653 -> failwith "impossible" in
                       let uu____5658 =
                         let uu____5659 = FStar_Syntax_Free.names p1 in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____5659 in
                       if uu____5658
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____5669 -> FStar_Pervasives_Native.None)
         | uu____5672 -> FStar_Pervasives_Native.None)
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____5703 =
      let uu____5716 =
        let uu____5717 = FStar_Syntax_Subst.compress t in
        uu____5717.FStar_Syntax_Syntax.n in
      match uu____5716 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____5826 =
            let uu____5835 =
              let uu____5836 = arrow bs c in
              FStar_Syntax_Syntax.mk_Total uu____5836 in
            (b, uu____5835) in
          FStar_Pervasives_Native.Some uu____5826
      | uu____5849 -> FStar_Pervasives_Native.None in
    FStar_Util.bind_opt uu____5703
      (fun uu____5885  ->
         match uu____5885 with
         | (b,c) ->
             let uu____5920 = FStar_Syntax_Subst.open_comp [b] c in
             (match uu____5920 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____5967 ->
                        failwith
                          "impossible: open_comp returned different amount of binders" in
                  FStar_Pervasives_Native.Some (b1, c1)))
let is_free_in:
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun bv  ->
    fun t  ->
      let uu____5992 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____5992
type qpats = FStar_Syntax_Syntax.args Prims.list[@@deriving show]
type connective =
  | QAll of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3
  | QEx of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3
  | BaseConn of (FStar_Ident.lident,FStar_Syntax_Syntax.args)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_QAll: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____6036 -> false
let __proj__QAll__item___0:
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QAll _0 -> _0
let uu___is_QEx: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____6074 -> false
let __proj__QEx__item___0:
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QEx _0 -> _0
let uu___is_BaseConn: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____6110 -> false
let __proj__BaseConn__item___0:
  connective ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | BaseConn _0 -> _0
let destruct_typ_as_formula:
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1 in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____6145) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____6157) ->
          unmeta_monadic t
      | uu____6170 -> f2 in
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
        (FStar_Parser_Const.eq3_lid, (Prims.parse_int "2"))] in
      let aux f2 uu____6248 =
        match uu____6248 with
        | (lid,arity) ->
            let uu____6257 =
              let uu____6272 = unmeta_monadic f2 in head_and_args uu____6272 in
            (match uu____6257 with
             | (t,args) ->
                 let t1 = un_uinst t in
                 let uu____6298 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity) in
                 if uu____6298
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None) in
      FStar_Util.find_map connectives (aux f1) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____6373 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____6373)
      | uu____6384 ->
          let uu____6385 = FStar_Syntax_Subst.compress t1 in ([], uu____6385) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu____6432 = head_and_args t1 in
        match uu____6432 with
        | (t2,args) ->
            let uu____6479 = un_uinst t2 in
            let uu____6480 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6513  ->
                      match uu____6513 with
                      | (t3,imp) ->
                          let uu____6524 = unascribe t3 in (uu____6524, imp))) in
            (uu____6479, uu____6480) in
      let rec aux qopt out t1 =
        let uu____6559 = let uu____6576 = flat t1 in (qopt, uu____6576) in
        match uu____6559 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____6603;
                 FStar_Syntax_Syntax.vars = uu____6604;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____6607);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____6608;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____6609;_},uu____6610)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____6687;
                 FStar_Syntax_Syntax.vars = uu____6688;_},uu____6689::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____6692);
                  FStar_Syntax_Syntax.pos = uu____6693;
                  FStar_Syntax_Syntax.vars = uu____6694;_},uu____6695)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____6783;
               FStar_Syntax_Syntax.vars = uu____6784;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____6787);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6788;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6789;_},uu____6790)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____6866;
               FStar_Syntax_Syntax.vars = uu____6867;_},uu____6868::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____6871);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6872;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____6873;_},uu____6874)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____6962) ->
            let bs = FStar_List.rev out in
            let uu____6996 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____6996 with
             | (bs1,t2) ->
                 let uu____7005 = patterns t2 in
                 (match uu____7005 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____7067 -> FStar_Pervasives_Native.None in
      aux FStar_Pervasives_Native.None [] t in
    let u_connectives =
      [(FStar_Parser_Const.true_lid, FStar_Parser_Const.c_true_lid,
         (Prims.parse_int "0"));
      (FStar_Parser_Const.false_lid, FStar_Parser_Const.c_false_lid,
        (Prims.parse_int "0"));
      (FStar_Parser_Const.and_lid, FStar_Parser_Const.c_and_lid,
        (Prims.parse_int "2"));
      (FStar_Parser_Const.or_lid, FStar_Parser_Const.c_or_lid,
        (Prims.parse_int "2"))] in
    let destruct_sq_base_conn t =
      let uu____7133 = un_squash t in
      FStar_Util.bind_opt uu____7133
        (fun t1  ->
           let uu____7149 = head_and_args' t1 in
           match uu____7149 with
           | (hd1,args) ->
               let uu____7182 =
                 let uu____7187 =
                   let uu____7188 = un_uinst hd1 in
                   uu____7188.FStar_Syntax_Syntax.n in
                 (uu____7187, (FStar_List.length args)) in
               (match uu____7182 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_30) when
                    (_0_30 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_31) when
                    (_0_31 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_32) when
                    (_0_32 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_33) when
                    (_0_33 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_34) when
                    (_0_34 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_35) when
                    (_0_35 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_36) when
                    (_0_36 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_37) when
                    (_0_37 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____7271 -> FStar_Pervasives_Native.None)) in
    let rec destruct_sq_forall t =
      let uu____7294 = un_squash t in
      FStar_Util.bind_opt uu____7294
        (fun t1  ->
           let uu____7309 = arrow_one t1 in
           match uu____7309 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____7324 =
                 let uu____7325 = is_tot_or_gtot_comp c in
                 Prims.op_Negation uu____7325 in
               if uu____7324
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____7332 = comp_to_comp_typ c in
                    uu____7332.FStar_Syntax_Syntax.result_typ in
                  let uu____7333 = FStar_Syntax_Subst.open_term [b] q in
                  match uu____7333 with
                  | (bs,q1) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____7364 -> failwith "impossible" in
                      let uu____7369 =
                        is_free_in (FStar_Pervasives_Native.fst b1) q1 in
                      if uu____7369
                      then
                        let uu____7372 = patterns q1 in
                        (match uu____7372 with
                         | (pats,q2) ->
                             FStar_All.pipe_left maybe_collect
                               (FStar_Pervasives_Native.Some
                                  (QAll ([b1], pats, q2))))
                      else
                        (let uu____7440 =
                           let uu____7441 =
                             let uu____7446 =
                               let uu____7449 =
                                 FStar_Syntax_Syntax.as_arg
                                   (FStar_Pervasives_Native.fst b1).FStar_Syntax_Syntax.sort in
                               let uu____7450 =
                                 let uu____7453 =
                                   FStar_Syntax_Syntax.as_arg q1 in
                                 [uu____7453] in
                               uu____7449 :: uu____7450 in
                             (FStar_Parser_Const.imp_lid, uu____7446) in
                           BaseConn uu____7441 in
                         FStar_Pervasives_Native.Some uu____7440))
           | uu____7456 -> FStar_Pervasives_Native.None)
    and destruct_sq_exists t =
      let uu____7464 = un_squash t in
      FStar_Util.bind_opt uu____7464
        (fun t1  ->
           let uu____7495 = head_and_args' t1 in
           match uu____7495 with
           | (hd1,args) ->
               let uu____7528 =
                 let uu____7541 =
                   let uu____7542 = un_uinst hd1 in
                   uu____7542.FStar_Syntax_Syntax.n in
                 (uu____7541, args) in
               (match uu____7528 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____7557)::(a2,uu____7559)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____7594 =
                      let uu____7595 = FStar_Syntax_Subst.compress a2 in
                      uu____7595.FStar_Syntax_Syntax.n in
                    (match uu____7594 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____7602) ->
                         let uu____7629 = FStar_Syntax_Subst.open_term [b] q in
                         (match uu____7629 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____7668 -> failwith "impossible" in
                              let uu____7673 = patterns q1 in
                              (match uu____7673 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____7740 -> FStar_Pervasives_Native.None)
                | uu____7741 -> FStar_Pervasives_Native.None))
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____7762 = destruct_sq_forall phi in
          (match uu____7762 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____7784 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____7790 = destruct_sq_exists phi in
          (match uu____7790 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____7812 -> f1)
      | uu____7815 -> f1 in
    let phi = unmeta_monadic f in
    let uu____7819 = destruct_base_conn phi in
    FStar_Util.catch_opt uu____7819
      (fun uu____7824  ->
         let uu____7825 = destruct_q_conn phi in
         FStar_Util.catch_opt uu____7825
           (fun uu____7830  ->
              let uu____7831 = destruct_sq_base_conn phi in
              FStar_Util.catch_opt uu____7831
                (fun uu____7836  ->
                   let uu____7837 = destruct_sq_forall phi in
                   FStar_Util.catch_opt uu____7837
                     (fun uu____7842  ->
                        let uu____7843 = destruct_sq_exists phi in
                        FStar_Util.catch_opt uu____7843
                          (fun uu____7847  -> FStar_Pervasives_Native.None)))))
let action_as_lb:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____7857 =
          let uu____7862 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational
              FStar_Pervasives_Native.None in
          FStar_Util.Inr uu____7862 in
        let uu____7863 =
          let uu____7864 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
          arrow a.FStar_Syntax_Syntax.action_params uu____7864 in
        let uu____7867 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None in
        close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____7857
          a.FStar_Syntax_Syntax.action_univs uu____7863
          FStar_Parser_Const.effect_Tot_lid uu____7867 in
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
let mk_reify:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let reify_ =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
    let uu____7893 =
      let uu____7896 =
        let uu____7897 =
          let uu____7912 =
            let uu____7915 = FStar_Syntax_Syntax.as_arg t in [uu____7915] in
          (reify_, uu____7912) in
        FStar_Syntax_Syntax.Tm_app uu____7897 in
      FStar_Syntax_Syntax.mk uu____7896 in
    uu____7893 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
let rec delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____7928 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____7954 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____7955 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____7956 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____7979 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____7996 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____7997 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____7998 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____8012) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____8017;
           FStar_Syntax_Syntax.index = uu____8018;
           FStar_Syntax_Syntax.sort = t2;_},uu____8020)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____8028) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____8034,uu____8035) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8077) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____8098,t2,uu____8100) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____8121,t2) -> delta_qualifier t2
let rec incr_delta_depth:
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth =
  fun d  ->
    match d with
    | FStar_Syntax_Syntax.Delta_equational  -> d
    | FStar_Syntax_Syntax.Delta_constant  ->
        FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        FStar_Syntax_Syntax.Delta_defined_at_level
          (i + (Prims.parse_int "1"))
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
let incr_delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  -> let uu____8149 = delta_qualifier t in incr_delta_depth uu____8149
let is_unknown: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____8154 =
      let uu____8155 = FStar_Syntax_Subst.compress t in
      uu____8155.FStar_Syntax_Syntax.n in
    match uu____8154 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____8158 -> false
let rec list_elements:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____8171 = let uu____8186 = unmeta e in head_and_args uu____8186 in
    match uu____8171 with
    | (head1,args) ->
        let uu____8213 =
          let uu____8226 =
            let uu____8227 = un_uinst head1 in
            uu____8227.FStar_Syntax_Syntax.n in
          (uu____8226, args) in
        (match uu____8213 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____8243) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____8263::(hd1,uu____8265)::(tl1,uu____8267)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____8314 =
               let uu____8319 =
                 let uu____8324 = list_elements tl1 in
                 FStar_Util.must uu____8324 in
               hd1 :: uu____8319 in
             FStar_Pervasives_Native.Some uu____8314
         | uu____8337 -> FStar_Pervasives_Native.None)
let rec apply_last:
  'Auu____8358 .
    ('Auu____8358 -> 'Auu____8358) ->
      'Auu____8358 Prims.list -> 'Auu____8358 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____8381 = f a in [uu____8381]
      | x::xs -> let uu____8386 = apply_last f xs in x :: uu____8386
let dm4f_lid:
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident =
  fun ed  ->
    fun name  ->
      let p = FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname in
      let p' =
        apply_last
          (fun s  ->
             Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))
          p in
      FStar_Ident.lid_of_path p' FStar_Range.dummyRange
let rec mk_list:
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____8427 =
            let uu____8430 =
              let uu____8431 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
              FStar_Syntax_Syntax.Tm_fvar uu____8431 in
            FStar_Syntax_Syntax.mk uu____8430 in
          uu____8427 FStar_Pervasives_Native.None rng in
        let cons1 args pos =
          let uu____8444 =
            let uu____8445 =
              let uu____8446 = ctor FStar_Parser_Const.cons_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____8446
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____8445 args in
          uu____8444 FStar_Pervasives_Native.None pos in
        let nil args pos =
          let uu____8458 =
            let uu____8459 =
              let uu____8460 = ctor FStar_Parser_Const.nil_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____8460
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____8459 args in
          uu____8458 FStar_Pervasives_Native.None pos in
        let uu____8463 =
          let uu____8464 =
            let uu____8465 = FStar_Syntax_Syntax.iarg typ in [uu____8465] in
          nil uu____8464 rng in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____8471 =
                 let uu____8472 = FStar_Syntax_Syntax.iarg typ in
                 let uu____8473 =
                   let uu____8476 = FStar_Syntax_Syntax.as_arg t in
                   let uu____8477 =
                     let uu____8480 = FStar_Syntax_Syntax.as_arg a in
                     [uu____8480] in
                   uu____8476 :: uu____8477 in
                 uu____8472 :: uu____8473 in
               cons1 uu____8471 t.FStar_Syntax_Syntax.pos) l uu____8463
let uvar_from_id:
  Prims.int ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun id1  ->
    fun t  ->
      let uu____8491 =
        let uu____8494 =
          let uu____8495 =
            let uu____8512 = FStar_Syntax_Unionfind.from_id id1 in
            (uu____8512, t) in
          FStar_Syntax_Syntax.Tm_uvar uu____8495 in
        FStar_Syntax_Syntax.mk uu____8494 in
      uu____8491 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec eqlist:
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq1  ->
    fun xs  ->
      fun ys  ->
        match (xs, ys) with
        | ([],[]) -> true
        | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
        | uu____8575 -> false
let eqsum:
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
          | uu____8678 -> false
let eqprod:
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) ->
        ('a,'b) FStar_Pervasives_Native.tuple2 ->
          ('a,'b) FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun e1  ->
    fun e2  ->
      fun x  ->
        fun y  ->
          match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
let eqopt:
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
        | uu____8826 -> false
let rec term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_app uu____8937 ->
            let uu____8952 = head_and_args' t in
            (match uu____8952 with
             | (hd1,args) ->
                 let uu___175_8985 = t in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.pos =
                     (uu___175_8985.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___175_8985.FStar_Syntax_Syntax.vars)
                 })
        | uu____8996 -> t in
      let t11 = let uu____9000 = unmeta_safe t1 in canon_app uu____9000 in
      let t21 = let uu____9006 = unmeta_safe t2 in canon_app uu____9006 in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
          x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
          FStar_Syntax_Syntax.bv_eq x y
      | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
          FStar_Syntax_Syntax.fv_eq x y
      | (FStar_Syntax_Syntax.Tm_uinst (t12,us1),FStar_Syntax_Syntax.Tm_uinst
         (t22,us2)) -> (eqlist eq_univs us1 us2) && (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
         c2) -> FStar_Const.eq_const c1 c2
      | (FStar_Syntax_Syntax.Tm_type x,FStar_Syntax_Syntax.Tm_type y) ->
          x = y
      | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
         (b2,t22,k2)) -> (eqlist binder_eq b1 b2) && (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
         (f2,a2)) -> (term_eq f1 f2) && (eqlist arg_eq a1 a2)
      | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
         (b2,c2)) -> (eqlist binder_eq b1 b2) && (comp_eq c1 c2)
      | (FStar_Syntax_Syntax.Tm_refine (b1,t12),FStar_Syntax_Syntax.Tm_refine
         (b2,t22)) -> (FStar_Syntax_Syntax.bv_eq b1 b2) && (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) -> (term_eq t12 t22) && (eqlist branch_eq bs1 bs2)
      | (uu____9273,uu____9274) -> false
and arg_eq:
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun a1  -> fun a2  -> eqprod term_eq (fun q1  -> fun q2  -> q1 = q2) a1 a2
and binder_eq:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun b1  ->
    fun b2  ->
      eqprod
        (fun b11  ->
           fun b21  ->
             term_eq b11.FStar_Syntax_Syntax.sort
               b21.FStar_Syntax_Syntax.sort) (fun q1  -> fun q2  -> q1 = q2)
        b1 b2
and lcomp_eq:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c1  -> fun c2  -> false
and residual_eq:
  FStar_Syntax_Syntax.residual_comp ->
    FStar_Syntax_Syntax.residual_comp -> Prims.bool
  = fun r1  -> fun r2  -> false
and comp_eq:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool
  =
  fun c1  ->
    fun c2  ->
      match ((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Total (t1,u1),FStar_Syntax_Syntax.Total (t2,u2))
          -> term_eq t1 t2
      | (FStar_Syntax_Syntax.GTotal (t1,u1),FStar_Syntax_Syntax.GTotal
         (t2,u2)) -> term_eq t1 t2
      | (FStar_Syntax_Syntax.Comp c11,FStar_Syntax_Syntax.Comp c21) ->
          ((((c11.FStar_Syntax_Syntax.comp_univs =
                c21.FStar_Syntax_Syntax.comp_univs)
               &&
               (c11.FStar_Syntax_Syntax.effect_name =
                  c21.FStar_Syntax_Syntax.effect_name))
              &&
              (term_eq c11.FStar_Syntax_Syntax.result_typ
                 c21.FStar_Syntax_Syntax.result_typ))
             &&
             (eqlist arg_eq c11.FStar_Syntax_Syntax.effect_args
                c21.FStar_Syntax_Syntax.effect_args))
            &&
            (eq_flags c11.FStar_Syntax_Syntax.flags
               c21.FStar_Syntax_Syntax.flags)
      | (uu____9369,uu____9370) -> false
and eq_flags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list -> Prims.bool
  = fun f1  -> fun f2  -> false
and branch_eq:
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax
                                                             FStar_Pervasives_Native.option,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                               FStar_Syntax_Syntax.syntax
                                                               FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu____9377  ->
    fun uu____9378  ->
      match (uu____9377, uu____9378) with | ((p1,w1,t1),(p2,w2,t2)) -> false
let rec bottom_fold:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f in
      let tn =
        let uu____9518 = FStar_Syntax_Subst.compress t in
        uu____9518.FStar_Syntax_Syntax.n in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____9544 =
              let uu____9559 = ff f1 in
              let uu____9560 =
                FStar_List.map
                  (fun uu____9579  ->
                     match uu____9579 with
                     | (a,q) -> let uu____9590 = ff a in (uu____9590, q))
                  args in
              (uu____9559, uu____9560) in
            FStar_Syntax_Syntax.Tm_app uu____9544
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____9620 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____9620 with
             | (bs1,t') ->
                 let t'' = ff t' in
                 let uu____9628 =
                   let uu____9645 = FStar_Syntax_Subst.close bs1 t'' in
                   (bs1, uu____9645, k) in
                 FStar_Syntax_Syntax.Tm_abs uu____9628)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____9672 = let uu____9679 = ff t1 in (uu____9679, us) in
            FStar_Syntax_Syntax.Tm_uinst uu____9672
        | uu____9680 -> tn in
      f
        (let uu___176_9683 = t in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.pos = (uu___176_9683.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___176_9683.FStar_Syntax_Syntax.vars)
         })
let rec sizeof: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____9688 ->
        let uu____9713 =
          let uu____9714 = FStar_Syntax_Subst.compress t in sizeof uu____9714 in
        (Prims.parse_int "1") + uu____9713
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____9716 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____9716
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____9718 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____9718
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____9725 = sizeof t1 in (FStar_List.length us) + uu____9725
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____9728) ->
        let uu____9749 = sizeof t1 in
        let uu____9750 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____9761  ->
                 match uu____9761 with
                 | (bv,uu____9767) ->
                     let uu____9768 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu____9768) (Prims.parse_int "0") bs in
        uu____9749 + uu____9750
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9791 = sizeof hd1 in
        let uu____9792 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____9803  ->
                 match uu____9803 with
                 | (arg,uu____9809) ->
                     let uu____9810 = sizeof arg in acc + uu____9810)
            (Prims.parse_int "0") args in
        uu____9791 + uu____9792
    | uu____9811 -> Prims.parse_int "1"
let is_synth_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____9816 =
      let uu____9817 = un_uinst t in uu____9817.FStar_Syntax_Syntax.n in
    match uu____9816 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
    | uu____9821 -> false
let mk_alien:
  'a .
    'a ->
      Prims.string ->
        FStar_Range.range FStar_Pervasives_Native.option ->
          FStar_Syntax_Syntax.term
  =
  fun b  ->
    fun s  ->
      fun r  ->
        let uu____9847 =
          let uu____9850 =
            let uu____9851 =
              let uu____9858 =
                let uu____9859 =
                  let uu____9864 = FStar_Dyn.mkdyn b in (uu____9864, s) in
                FStar_Syntax_Syntax.Meta_alien uu____9859 in
              (FStar_Syntax_Syntax.tun, uu____9858) in
            FStar_Syntax_Syntax.Tm_meta uu____9851 in
          FStar_Syntax_Syntax.mk uu____9850 in
        uu____9847 FStar_Pervasives_Native.None
          (match r with
           | FStar_Pervasives_Native.Some r1 -> r1
           | FStar_Pervasives_Native.None  -> FStar_Range.dummyRange)
let un_alien: FStar_Syntax_Syntax.term -> FStar_Dyn.dyn =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        (uu____9876,FStar_Syntax_Syntax.Meta_alien (blob,uu____9878)) -> blob
    | uu____9883 -> failwith "unexpected: term was not an alien embedding"