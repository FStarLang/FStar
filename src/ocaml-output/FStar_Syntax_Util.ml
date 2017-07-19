open Prims
let qual_id: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun id  ->
      let uu____9 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id]) in
      FStar_Ident.set_lid_range uu____9 id.FStar_Ident.idRange
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
let arg_of_non_null_binder uu____35 =
  match uu____35 with
  | (b,imp) ->
      let uu____42 = FStar_Syntax_Syntax.bv_to_name b in (uu____42, imp)
let args_of_non_null_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____66 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____66
            then []
            else (let uu____78 = arg_of_non_null_binder b in [uu____78])))
let args_of_binders:
  FStar_Syntax_Syntax.binders ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,(FStar_Syntax_Syntax.term,
                                                   FStar_Syntax_Syntax.aqual)
                                                   FStar_Pervasives_Native.tuple2
                                                   Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun binders  ->
    let uu____103 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____149 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____149
              then
                let b1 =
                  let uu____167 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  (uu____167, (FStar_Pervasives_Native.snd b)) in
                let uu____168 = arg_of_non_null_binder b1 in (b1, uu____168)
              else
                (let uu____182 = arg_of_non_null_binder b in (b, uu____182)))) in
    FStar_All.pipe_right uu____103 FStar_List.unzip
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
              let uu____265 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____265
              then
                let uu____270 = b in
                match uu____270 with
                | (a,imp) ->
                    let b1 =
                      let uu____278 =
                        let uu____279 = FStar_Util.string_of_int i in
                        Prims.strcat "_" uu____279 in
                      FStar_Ident.id_of_text uu____278 in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      } in
                    (b2, imp)
              else b))
let name_function_binders t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
      let uu____325 =
        let uu____330 =
          let uu____331 =
            let uu____346 = name_binders binders in (uu____346, comp) in
          FStar_Syntax_Syntax.Tm_arrow uu____331 in
        FStar_Syntax_Syntax.mk uu____330 in
      uu____325 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  | uu____367 -> t
let null_binders_of_tks:
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____408  ->
            match uu____408 with
            | (t,imp) ->
                let uu____419 =
                  let uu____420 = FStar_Syntax_Syntax.null_binder t in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____420 in
                (uu____419, imp)))
let binders_of_tks:
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____473  ->
            match uu____473 with
            | (t,imp) ->
                let uu____496 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t in
                (uu____496, imp)))
let binders_of_freevars:
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list
  =
  fun fvs  ->
    let uu____507 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____507
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
let mk_subst s = [s]
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
          (fun uu____619  ->
             fun uu____620  ->
               match (uu____619, uu____620) with
               | ((x,uu____638),(y,uu____640)) ->
                   let uu____649 =
                     let uu____658 = FStar_Syntax_Syntax.bv_to_name y in
                     (x, uu____658) in
                   FStar_Syntax_Syntax.NT uu____649) replace_xs with_ys
      else failwith "Ill-formed substitution"
let rec unmeta: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____666) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____676,uu____677) -> unmeta e2
    | uu____734 -> e1
let rec univ_kernel:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____747 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____748 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____758 = univ_kernel u1 in
        (match uu____758 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____769 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____776 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let constant_univ_as_nat: FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  ->
    let uu____785 = univ_kernel u in FStar_Pervasives_Native.snd uu____785
let rec compare_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____798,uu____799) ->
          failwith "Impossible: compare_univs"
      | (uu____800,FStar_Syntax_Syntax.U_bvar uu____801) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_unknown ,uu____802) -> - (Prims.parse_int "1")
      | (uu____803,FStar_Syntax_Syntax.U_unknown ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_zero ,uu____804) -> - (Prims.parse_int "1")
      | (uu____805,FStar_Syntax_Syntax.U_zero ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____808,FStar_Syntax_Syntax.U_unif
         uu____809) -> - (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____818,FStar_Syntax_Syntax.U_name
         uu____819) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____846 = FStar_Syntax_Unionfind.univ_uvar_id u11 in
          let uu____847 = FStar_Syntax_Unionfind.univ_uvar_id u21 in
          uu____846 - uu____847
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1 in
          let n2 = FStar_List.length us2 in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____878 = FStar_List.zip us1 us2 in
               FStar_Util.find_map uu____878
                 (fun uu____893  ->
                    match uu____893 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21 in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None) in
             match copt with
             | FStar_Pervasives_Native.None  -> Prims.parse_int "0"
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____907,uu____908) ->
          - (Prims.parse_int "1")
      | (uu____911,FStar_Syntax_Syntax.U_max uu____912) ->
          Prims.parse_int "1"
      | uu____915 ->
          let uu____920 = univ_kernel u1 in
          (match uu____920 with
           | (k1,n1) ->
               let uu____927 = univ_kernel u2 in
               (match uu____927 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2 in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
let eq_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____944 = compare_univs u1 u2 in
      uu____944 = (Prims.parse_int "0")
let ml_comp:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
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
let comp_effect_name c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
  | FStar_Syntax_Syntax.Total uu____987 -> FStar_Parser_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.GTotal uu____998 ->
      FStar_Parser_Const.effect_GTot_lid
let comp_flags c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____1028 -> [FStar_Syntax_Syntax.TOTAL]
  | FStar_Syntax_Syntax.GTotal uu____1039 ->
      [FStar_Syntax_Syntax.SOMETRIVIAL]
  | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
let comp_set_flags:
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    fun f  ->
      let comp_to_comp_typ c1 =
        match c1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Comp c2 -> c2
        | FStar_Syntax_Syntax.Total (t,u_opt) ->
            let uu____1086 =
              let uu____1087 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____1087 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____1086;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
        | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
            let uu____1120 =
              let uu____1121 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____1121 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____1120;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            } in
      let uu___165_1140 = c in
      let uu____1141 =
        let uu____1142 =
          let uu___166_1143 = comp_to_comp_typ c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___166_1143.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___166_1143.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___166_1143.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___166_1143.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu____1142 in
      {
        FStar_Syntax_Syntax.n = uu____1141;
        FStar_Syntax_Syntax.tk = (uu___165_1140.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = (uu___165_1140.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___165_1140.FStar_Syntax_Syntax.vars)
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
    | uu____1189 ->
        failwith "Assertion failed: Computation type without universe"
let is_named_tot c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.Total uu____1208 -> true
  | FStar_Syntax_Syntax.GTotal uu____1219 -> false
let is_total_comp c =
  (FStar_Ident.lid_equals (comp_effect_name c)
     FStar_Parser_Const.effect_Tot_lid)
    ||
    (FStar_All.pipe_right (comp_flags c)
       (FStar_Util.for_some
          (fun uu___153_1250  ->
             match uu___153_1250 with
             | FStar_Syntax_Syntax.TOTAL  -> true
             | FStar_Syntax_Syntax.RETURN  -> true
             | uu____1251 -> false)))
let is_total_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___154_1259  ->
               match uu___154_1259 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1260 -> false)))
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
            (fun uu___155_1268  ->
               match uu___155_1268 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1269 -> false)))
let is_partial_return c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___156_1290  ->
          match uu___156_1290 with
          | FStar_Syntax_Syntax.RETURN  -> true
          | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
          | uu____1291 -> false))
let is_lcomp_partial_return: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___157_1299  ->
            match uu___157_1299 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1300 -> false))
let is_tot_or_gtot_comp c =
  (is_total_comp c) ||
    (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid
       (comp_effect_name c))
let is_pure_effect: FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)
let is_pure_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____1339 -> true
  | FStar_Syntax_Syntax.GTotal uu____1350 -> false
  | FStar_Syntax_Syntax.Comp ct ->
      ((is_total_comp c) ||
         (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
        ||
        (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___158_1365  ->
                 match uu___158_1365 with
                 | FStar_Syntax_Syntax.LEMMA  -> true
                 | uu____1366 -> false)))
let is_ghost_effect: FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)
let is_pure_or_ghost_comp c =
  (is_pure_comp c) || (is_ghost_effect (comp_effect_name c))
let is_pure_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___159_1395  ->
               match uu___159_1395 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1396 -> false)))
let is_pure_or_ghost_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
let is_pure_or_ghost_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1405 =
      let uu____1406 = FStar_Syntax_Subst.compress t in
      uu____1406.FStar_Syntax_Syntax.n in
    match uu____1405 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1411,c) -> is_pure_or_ghost_comp c
    | uu____1433 -> true
let is_lemma_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
  | uu____1452 -> false
let is_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1457 =
      let uu____1458 = FStar_Syntax_Subst.compress t in
      uu____1458.FStar_Syntax_Syntax.n in
    match uu____1457 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1463,c) -> is_lemma_comp c
    | uu____1485 -> false
let head_and_args:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
       FStar_Syntax_Syntax.syntax,((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                     FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
                                    FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____1571 -> (t1, [])
let rec head_and_args':
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                 FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1653 = head_and_args' head1 in
        (match uu____1653 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1722 -> (t1, [])
let un_uinst: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1747) ->
        FStar_Syntax_Subst.compress t2
    | uu____1756 -> t1
let is_smt_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1761 =
      let uu____1762 = FStar_Syntax_Subst.compress t in
      uu____1762.FStar_Syntax_Syntax.n in
    match uu____1761 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1767,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1793)::uu____1794 ->
                  let pats' = unmeta pats in
                  let uu____1854 = head_and_args pats' in
                  (match uu____1854 with
                   | (head1,uu____1874) ->
                       let uu____1903 =
                         let uu____1904 = un_uinst head1 in
                         uu____1904.FStar_Syntax_Syntax.n in
                       (match uu____1903 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1910 -> false))
              | uu____1911 -> false)
         | uu____1922 -> false)
    | uu____1923 -> false
let is_ml_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
         FStar_Parser_Const.effect_ML_lid)
        ||
        (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___160_1945  ->
                 match uu___160_1945 with
                 | FStar_Syntax_Syntax.MLEFFECT  -> true
                 | uu____1946 -> false)))
  | uu____1947 -> false
let comp_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,uu____1970) -> t
  | FStar_Syntax_Syntax.GTotal (t,uu____1984) -> t
  | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let set_result_typ c t =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____2021 -> FStar_Syntax_Syntax.mk_Total t
  | FStar_Syntax_Syntax.GTotal uu____2032 -> FStar_Syntax_Syntax.mk_GTotal t
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Syntax_Syntax.mk_Comp
        (let uu___167_2046 = ct in
         {
           FStar_Syntax_Syntax.comp_univs =
             (uu___167_2046.FStar_Syntax_Syntax.comp_univs);
           FStar_Syntax_Syntax.effect_name =
             (uu___167_2046.FStar_Syntax_Syntax.effect_name);
           FStar_Syntax_Syntax.result_typ = t;
           FStar_Syntax_Syntax.effect_args =
             (uu___167_2046.FStar_Syntax_Syntax.effect_args);
           FStar_Syntax_Syntax.flags =
             (uu___167_2046.FStar_Syntax_Syntax.flags)
         })
let is_trivial_wp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___161_2067  ->
          match uu___161_2067 with
          | FStar_Syntax_Syntax.TOTAL  -> true
          | FStar_Syntax_Syntax.RETURN  -> true
          | uu____2068 -> false))
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
let is_primop f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      is_primop_lid (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____2095 -> false
let rec unascribe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____2102,uu____2103) ->
        unascribe e2
    | uu____2160 -> e1
let rec ascribe t k =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_ascribed (t',uu____2233,uu____2234) ->
      ascribe t' k
  | uu____2291 ->
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_ascribed (t, k, FStar_Pervasives_Native.None))
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
type eq_result =
  | Equal
  | NotEqual
  | Unknown
let uu___is_Equal: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2324 -> false
let uu___is_NotEqual: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2329 -> false
let uu___is_Unknown: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2334 -> false
let rec eq_tm:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        let uu____2357 =
          let uu____2372 = unascribe t in head_and_args' uu____2372 in
        match uu____2357 with
        | (hd1,args) ->
            FStar_Syntax_Syntax.mk_Tm_app hd1 args
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
      let equal_if uu___162_2412 = if uu___162_2412 then Equal else Unknown in
      let equal_iff uu___163_2417 = if uu___163_2417 then Equal else NotEqual in
      let eq_and f g = match f with | Equal  -> g () | uu____2431 -> Unknown in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2439) -> NotEqual
        | (uu____2440,NotEqual ) -> NotEqual
        | (Unknown ,uu____2441) -> Unknown
        | (uu____2442,Unknown ) -> Unknown in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____2447 = FStar_Syntax_Syntax.fv_eq f g in
          equal_if uu____2447
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2468 = eq_tm f g in
          eq_and uu____2468
            (fun uu____2471  ->
               let uu____2472 = eq_univs_list us vs in equal_if uu____2472)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2475 = FStar_Const.eq_const c d in equal_iff uu____2475
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2477),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2479)) ->
          let uu____2544 = FStar_Syntax_Unionfind.equiv u1 u2 in
          equal_if uu____2544
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2605 =
            let uu____2610 =
              let uu____2611 = un_uinst h1 in
              uu____2611.FStar_Syntax_Syntax.n in
            let uu____2616 =
              let uu____2617 = un_uinst h2 in
              uu____2617.FStar_Syntax_Syntax.n in
            (uu____2610, uu____2616) in
          (match uu____2605 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (f1.FStar_Syntax_Syntax.fv_qual =
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
                 &&
                 (f2.FStar_Syntax_Syntax.fv_qual =
                    (FStar_Pervasives_Native.Some
                       FStar_Syntax_Syntax.Data_ctor))
               ->
               let uu____2628 = FStar_Syntax_Syntax.fv_eq f1 f2 in
               if uu____2628
               then
                 let uu____2632 = FStar_List.zip args1 args2 in
                 FStar_All.pipe_left
                   (FStar_List.fold_left
                      (fun acc  ->
                         fun uu____2698  ->
                           match uu____2698 with
                           | ((a1,q1),(a2,q2)) ->
                               let uu____2726 = eq_tm a1 a2 in
                               eq_inj acc uu____2726) Equal) uu____2632
               else NotEqual
           | uu____2728 ->
               let uu____2733 = eq_tm h1 h2 in
               eq_and uu____2733 (fun uu____2735  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____2738 = eq_univs u v1 in equal_if uu____2738
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____2740),uu____2741) ->
          eq_tm t12 t21
      | (uu____2750,FStar_Syntax_Syntax.Tm_meta (t22,uu____2752)) ->
          eq_tm t11 t22
      | uu____2761 -> Unknown
and eq_args:
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____2805)::a11,(b,uu____2808)::b1) ->
          let uu____2882 = eq_tm a b in
          (match uu____2882 with
           | Equal  -> eq_args a11 b1
           | uu____2883 -> Unknown)
      | uu____2884 -> Unknown
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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____2897) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2907,uu____2908) ->
        unrefine t2
    | uu____2965 -> t1
let rec is_unit: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2970 =
      let uu____2971 = unrefine t in uu____2971.FStar_Syntax_Syntax.n in
    match uu____2970 with
    | FStar_Syntax_Syntax.Tm_type uu____2976 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2979) -> is_unit t1
    | uu____2988 -> false
let rec non_informative: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2993 =
      let uu____2994 = unrefine t in uu____2994.FStar_Syntax_Syntax.n in
    match uu____2993 with
    | FStar_Syntax_Syntax.Tm_type uu____2999 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3002) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3032) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3041,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3063 -> false
let is_fun: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____3068 =
      let uu____3069 = FStar_Syntax_Subst.compress e in
      uu____3069.FStar_Syntax_Syntax.n in
    match uu____3068 with
    | FStar_Syntax_Syntax.Tm_abs uu____3074 -> true
    | uu____3093 -> false
let is_function_typ: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3098 =
      let uu____3099 = FStar_Syntax_Subst.compress t in
      uu____3099.FStar_Syntax_Syntax.n in
    match uu____3098 with
    | FStar_Syntax_Syntax.Tm_arrow uu____3104 -> true
    | uu____3119 -> false
let rec pre_typ: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3126) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3136,uu____3137) ->
        pre_typ t2
    | uu____3194 -> t1
let destruct:
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ in
      let uu____3216 =
        let uu____3217 = un_uinst typ1 in uu____3217.FStar_Syntax_Syntax.n in
      match uu____3216 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1 in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____3288 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____3318 -> FStar_Pervasives_Native.None
let lids_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____3337,lids) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____3343,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3354,uu____3355,uu____3356,uu____3357,uu____3358) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____3368,uu____3369,uu____3370,uu____3371) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____3377,uu____3378,uu____3379,uu____3380,uu____3381) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3387,uu____3388) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3390,uu____3391) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3394 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____3395 -> []
    | FStar_Syntax_Syntax.Sig_main uu____3396 -> []
let lid_of_sigelt:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____3408 -> FStar_Pervasives_Native.None
let quals_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals
let range_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng
let range_of_lb uu___164_3442 =
  match uu___164_3442 with
  | (FStar_Util.Inl x,uu____3454,uu____3455) ->
      FStar_Syntax_Syntax.range_of_bv x
  | (FStar_Util.Inr l,uu____3461,uu____3462) -> FStar_Ident.range_of_lid l
let range_of_arg uu____3489 =
  match uu____3489 with | (hd1,uu____3499) -> hd1.FStar_Syntax_Syntax.pos
let range_of_args args r =
  FStar_All.pipe_right args
    (FStar_List.fold_left
       (fun r1  -> fun a  -> FStar_Range.union_ranges r1 (range_of_arg a)) r)
let mk_app f args =
  let r = range_of_args args f.FStar_Syntax_Syntax.pos in
  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args))
    FStar_Pervasives_Native.None r
let mk_data l args =
  match args with
  | [] ->
      let uu____3688 =
        let uu____3693 =
          let uu____3694 =
            let uu____3703 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            (uu____3703,
              (FStar_Syntax_Syntax.Meta_desugared
                 FStar_Syntax_Syntax.Data_app)) in
          FStar_Syntax_Syntax.Tm_meta uu____3694 in
        FStar_Syntax_Syntax.mk uu____3693 in
      uu____3688 FStar_Pervasives_Native.None (FStar_Ident.range_of_lid l)
  | uu____3708 ->
      let e =
        let uu____3724 =
          FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
        mk_app uu____3724 args in
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_meta
           (e,
             (FStar_Syntax_Syntax.Meta_desugared FStar_Syntax_Syntax.Data_app)))
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
      let uu____3741 =
        let uu____3746 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9") in
        (uu____3746, (x.FStar_Ident.idRange)) in
      FStar_Ident.mk_ident uu____3741
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
          let uu____3789 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____3789
          then
            let uu____3790 =
              let uu____3795 =
                let uu____3796 = FStar_Util.string_of_int i in
                Prims.strcat "_" uu____3796 in
              let uu____3797 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____3795, uu____3797) in
            FStar_Ident.mk_ident uu____3790
          else x.FStar_Syntax_Syntax.ppname in
        let y =
          let uu___168_3800 = x in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___168_3800.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___168_3800.FStar_Syntax_Syntax.sort)
          } in
        let uu____3801 = mk_field_projector_name_from_ident lid nm in
        (uu____3801, y)
let set_uvar:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun uv  ->
    fun t  ->
      let uu____3810 = FStar_Syntax_Unionfind.find uv in
      match uu____3810 with
      | FStar_Pervasives_Native.Some uu____3813 ->
          let uu____3814 =
            let uu____3815 =
              let uu____3816 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu____3816 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3815 in
          failwith uu____3814
      | uu____3817 -> FStar_Syntax_Unionfind.change uv t
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
      | uu____3890 -> q1 = q2
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
              let uu____3924 =
                let uu___169_3925 = rc in
                let uu____3926 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs) in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___169_3925.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____3926;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___169_3925.FStar_Syntax_Syntax.residual_flags)
                } in
              FStar_Pervasives_Native.Some uu____3924 in
        match bs with
        | [] -> t
        | uu____3941 ->
            let body =
              let uu____3943 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____3943 in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____3975 =
                   let uu____3980 =
                     let uu____3981 =
                       let uu____4000 =
                         let uu____4007 = FStar_Syntax_Subst.close_binders bs in
                         FStar_List.append uu____4007 bs' in
                       let uu____4018 = close_lopt lopt' in
                       (uu____4000, t1, uu____4018) in
                     FStar_Syntax_Syntax.Tm_abs uu____3981 in
                   FStar_Syntax_Syntax.mk uu____3980 in
                 uu____3975 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4037 ->
                 let uu____4044 =
                   let uu____4049 =
                     let uu____4050 =
                       let uu____4069 = FStar_Syntax_Subst.close_binders bs in
                       let uu____4070 = close_lopt lopt in
                       (uu____4069, body, uu____4070) in
                     FStar_Syntax_Syntax.Tm_abs uu____4050 in
                   FStar_Syntax_Syntax.mk uu____4049 in
                 uu____4044 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos)
let arrow:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____4119 ->
          let uu____4126 =
            let uu____4131 =
              let uu____4132 =
                let uu____4147 = FStar_Syntax_Subst.close_binders bs in
                let uu____4148 = FStar_Syntax_Subst.close_comp bs c in
                (uu____4147, uu____4148) in
              FStar_Syntax_Syntax.Tm_arrow uu____4132 in
            FStar_Syntax_Syntax.mk uu____4131 in
          uu____4126 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
let flat_arrow:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c in
      let uu____4190 =
        let uu____4191 = FStar_Syntax_Subst.compress t in
        uu____4191.FStar_Syntax_Syntax.n in
      match uu____4190 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____4227) ->
               let uu____4240 =
                 let uu____4241 = FStar_Syntax_Subst.compress tres in
                 uu____4241.FStar_Syntax_Syntax.n in
               (match uu____4240 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    let uu____4272 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c')) uu____4272
                      t.FStar_Syntax_Syntax.pos
                | uu____4291 -> t)
           | uu____4292 -> t)
      | uu____4293 -> t
let refine:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____4306 =
        FStar_ST.read (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
      let uu____4311 =
        let uu____4312 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____4312 t.FStar_Syntax_Syntax.pos in
      let uu____4313 =
        let uu____4318 =
          let uu____4319 =
            let uu____4328 =
              let uu____4329 =
                let uu____4330 = FStar_Syntax_Syntax.mk_binder b in
                [uu____4330] in
              FStar_Syntax_Subst.close uu____4329 t in
            (b, uu____4328) in
          FStar_Syntax_Syntax.Tm_refine uu____4319 in
        FStar_Syntax_Syntax.mk uu____4318 in
      uu____4313 uu____4306 uu____4311
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
        let uu____4386 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4386 with
         | (bs1,c1) ->
             let uu____4403 = is_tot_or_gtot_comp c1 in
             if uu____4403
             then
               let uu____4414 = arrow_formals_comp (comp_result c1) in
               (match uu____4414 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____4460 ->
        let uu____4461 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____4461)
let rec arrow_formals:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,(FStar_Syntax_Syntax.term',
                                                   FStar_Syntax_Syntax.term')
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let uu____4490 = arrow_formals_comp k in
    match uu____4490 with | (bs,c) -> (bs, (comp_result c))
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
          let uu____4571 =
            let uu___170_4572 = rc in
            let uu____4573 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___170_4572.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____4573;
              FStar_Syntax_Syntax.residual_flags =
                (uu___170_4572.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____4571
      | uu____4584 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____4612 =
        let uu____4613 =
          let uu____4618 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____4618 in
        uu____4613.FStar_Syntax_Syntax.n in
      match uu____4612 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____4660 = aux t2 what in
          (match uu____4660 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____4720 -> ([], t1, abs_body_lcomp) in
    let uu____4733 = aux t FStar_Pervasives_Native.None in
    match uu____4733 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____4775 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____4775 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp in
             (bs1, t2, abs_body_lcomp1))
let mk_letbinding:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.letbinding
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
                | (FStar_Pervasives_Native.None ,uu____4897) -> def
                | (uu____4908,[]) -> def
                | (FStar_Pervasives_Native.Some fvs,uu____4920) ->
                    let universes =
                      FStar_All.pipe_right univ_vars
                        (FStar_List.map
                           (fun _0_26  -> FStar_Syntax_Syntax.U_name _0_26)) in
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
            let uu____5023 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____5023 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5052 ->
            let t' = arrow binders c in
            let uu____5064 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____5064 with
             | (uvs1,t'1) ->
                 let uu____5083 =
                   let uu____5084 = FStar_Syntax_Subst.compress t'1 in
                   uu____5084.FStar_Syntax_Syntax.n in
                 (match uu____5083 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____5133 -> failwith "Impossible"))
let is_tuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____5151 -> false
let is_dtuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____5157 -> false
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
      let uu____5197 =
        let uu____5198 = pre_typ t in uu____5198.FStar_Syntax_Syntax.n in
      match uu____5197 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____5204 -> false
let rec is_constructed_typ:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____5213 =
        let uu____5214 = pre_typ t in uu____5214.FStar_Syntax_Syntax.n in
      match uu____5213 with
      | FStar_Syntax_Syntax.Tm_fvar uu____5219 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____5221) ->
          is_constructed_typ t1 lid
      | uu____5250 -> false
let rec get_tycon:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____5260 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____5261 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____5262 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5264) -> get_tycon t2
    | uu____5293 -> FStar_Pervasives_Native.None
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
    let uu____5305 =
      let uu____5306 = un_uinst t in uu____5306.FStar_Syntax_Syntax.n in
    match uu____5305 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Parser_Const.fstar_refl_embed_lid
    | uu____5312 -> false
let is_fstar_tactics_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____5317 =
      let uu____5318 = un_uinst t in uu____5318.FStar_Syntax_Syntax.n in
    match uu____5317 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____5324 -> false
let ktype:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
let ktype0:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
let type_u:
  Prims.unit ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
       FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____5340  ->
    let u =
      let uu____5346 = FStar_Syntax_Unionfind.univ_fresh () in
      FStar_All.pipe_left (fun _0_27  -> FStar_Syntax_Syntax.U_unif _0_27)
        uu____5346 in
    let uu____5363 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange in
    (uu____5363, u)
let exp_true_bool:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
let exp_false_bool:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
let exp_unit:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
let exp_int:
  Prims.string ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_int (s, FStar_Pervasives_Native.None)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
let exp_string:
  Prims.string ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string
            ((FStar_Util.unicode_of_string s), FStar_Range.dummyRange)))
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
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu____5425 =
            let uu____5430 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            let uu____5431 =
              let uu____5436 =
                let uu____5437 =
                  let uu____5456 =
                    let uu____5459 = FStar_Syntax_Syntax.as_arg phi11 in
                    let uu____5460 =
                      let uu____5463 = FStar_Syntax_Syntax.as_arg phi2 in
                      [uu____5463] in
                    uu____5459 :: uu____5460 in
                  (tand, uu____5456) in
                FStar_Syntax_Syntax.Tm_app uu____5437 in
              FStar_Syntax_Syntax.mk uu____5436 in
            uu____5431 FStar_Pervasives_Native.None uu____5430 in
          FStar_Pervasives_Native.Some uu____5425
let mk_binop op_t phi1 phi2 =
  let uu____5507 =
    FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
      phi2.FStar_Syntax_Syntax.pos in
  let uu____5508 =
    let uu____5513 =
      let uu____5514 =
        let uu____5533 =
          let uu____5536 = FStar_Syntax_Syntax.as_arg phi1 in
          let uu____5537 =
            let uu____5540 = FStar_Syntax_Syntax.as_arg phi2 in [uu____5540] in
          uu____5536 :: uu____5537 in
        (op_t, uu____5533) in
      FStar_Syntax_Syntax.Tm_app uu____5514 in
    FStar_Syntax_Syntax.mk uu____5513 in
  uu____5508 FStar_Pervasives_Native.None uu____5507
let mk_neg phi =
  let uu____5564 =
    let uu____5569 =
      let uu____5570 =
        let uu____5589 =
          let uu____5592 = FStar_Syntax_Syntax.as_arg phi in [uu____5592] in
        (t_not, uu____5589) in
      FStar_Syntax_Syntax.Tm_app uu____5570 in
    FStar_Syntax_Syntax.mk uu____5569 in
  uu____5564 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
let mk_conj phi1 phi2 = mk_binop tand phi1 phi2
let mk_conj_l:
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
let mk_disj phi1 phi2 = mk_binop tor phi1 phi2
let mk_disj_l:
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
let mk_imp:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun phi1  -> fun phi2  -> mk_binop timp phi1 phi2
let mk_iff:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun phi1  -> fun phi2  -> mk_binop tiff phi1 phi2
let b2t e =
  let uu____5690 =
    let uu____5695 =
      let uu____5696 =
        let uu____5715 =
          let uu____5718 = FStar_Syntax_Syntax.as_arg e in [uu____5718] in
        (b2t_v, uu____5715) in
      FStar_Syntax_Syntax.Tm_app uu____5696 in
    FStar_Syntax_Syntax.mk uu____5695 in
  uu____5690 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
let teq: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.eq2_lid
let mk_untyped_eq2 e1 e2 =
  let uu____5744 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos in
  let uu____5745 =
    let uu____5750 =
      let uu____5751 =
        let uu____5770 =
          let uu____5773 = FStar_Syntax_Syntax.as_arg e1 in
          let uu____5774 =
            let uu____5777 = FStar_Syntax_Syntax.as_arg e2 in [uu____5777] in
          uu____5773 :: uu____5774 in
        (teq, uu____5770) in
      FStar_Syntax_Syntax.Tm_app uu____5751 in
    FStar_Syntax_Syntax.mk uu____5750 in
  uu____5745 FStar_Pervasives_Native.None uu____5744
let mk_eq2:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax
  =
  fun u  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          let eq_inst = FStar_Syntax_Syntax.mk_Tm_uinst teq [u] in
          let uu____5801 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          let uu____5802 =
            let uu____5807 =
              let uu____5808 =
                let uu____5827 =
                  let uu____5830 = FStar_Syntax_Syntax.iarg t in
                  let uu____5831 =
                    let uu____5834 = FStar_Syntax_Syntax.as_arg e1 in
                    let uu____5835 =
                      let uu____5838 = FStar_Syntax_Syntax.as_arg e2 in
                      [uu____5838] in
                    uu____5834 :: uu____5835 in
                  uu____5830 :: uu____5831 in
                (eq_inst, uu____5827) in
              FStar_Syntax_Syntax.Tm_app uu____5808 in
            FStar_Syntax_Syntax.mk uu____5807 in
          uu____5802 FStar_Pervasives_Native.None uu____5801
let mk_has_type t x t' =
  let t_has_type = fvar_const FStar_Parser_Const.has_type_lid in
  let t_has_type1 =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uinst
         (t_has_type,
           [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]))
      FStar_Pervasives_Native.None FStar_Range.dummyRange in
  let uu____5878 =
    let uu____5883 =
      let uu____5884 =
        let uu____5903 =
          let uu____5906 = FStar_Syntax_Syntax.iarg t in
          let uu____5907 =
            let uu____5910 = FStar_Syntax_Syntax.as_arg x in
            let uu____5911 =
              let uu____5914 = FStar_Syntax_Syntax.as_arg t' in [uu____5914] in
            uu____5910 :: uu____5911 in
          uu____5906 :: uu____5907 in
        (t_has_type1, uu____5903) in
      FStar_Syntax_Syntax.Tm_app uu____5884 in
    FStar_Syntax_Syntax.mk uu____5883 in
  uu____5878 FStar_Pervasives_Native.None FStar_Range.dummyRange
let lex_t: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.lex_t_lid
let lex_top:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  let uu____5929 =
    let uu____5934 =
      let uu____5935 =
        let uu____5944 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
        (uu____5944, [FStar_Syntax_Syntax.U_zero]) in
      FStar_Syntax_Syntax.Tm_uinst uu____5935 in
    FStar_Syntax_Syntax.mk uu____5934 in
  uu____5929 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.lcomp
  =
  fun c0  ->
    let uu____5963 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____5976 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____5989 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags)) in
    match uu____5963 with
    | (eff_name,flags) ->
        {
          FStar_Syntax_Syntax.eff_name = eff_name;
          FStar_Syntax_Syntax.res_typ = (comp_result c0);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = ((fun uu____6012  -> c0))
        }
let mk_residual_comp:
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option ->
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
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.residual_comp
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
let mk_forall_aux fa x body =
  let uu____6106 =
    let uu____6111 =
      let uu____6112 =
        let uu____6131 =
          let uu____6134 =
            FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
          let uu____6135 =
            let uu____6138 =
              let uu____6139 =
                let uu____6140 =
                  let uu____6141 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____6141] in
                abs uu____6140 body
                  (FStar_Pervasives_Native.Some (residual_tot ktype0)) in
              FStar_Syntax_Syntax.as_arg uu____6139 in
            [uu____6138] in
          uu____6134 :: uu____6135 in
        (fa, uu____6131) in
      FStar_Syntax_Syntax.Tm_app uu____6112 in
    FStar_Syntax_Syntax.mk uu____6111 in
  uu____6106 FStar_Pervasives_Native.None FStar_Range.dummyRange
let mk_forall_no_univ:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun x  -> fun body  -> mk_forall_aux tforall x body
let mk_forall:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax
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
             let uu____6190 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____6190
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
let rec is_wild_pat:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____6200 -> true
    | uu____6201 -> false
let if_then_else b t1 t2 =
  let then_branch =
    let uu____6270 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
        t1.FStar_Syntax_Syntax.pos in
    (uu____6270, FStar_Pervasives_Native.None, t1) in
  let else_branch =
    let uu____6308 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool false))
        t2.FStar_Syntax_Syntax.pos in
    (uu____6308, FStar_Pervasives_Native.None, t2) in
  let uu____6327 =
    let uu____6328 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____6328 in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
    FStar_Pervasives_Native.None uu____6327
let mk_squash p =
  let sq =
    FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
      (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
      FStar_Pervasives_Native.None in
  let uu____6421 =
    FStar_Syntax_Syntax.mk_Tm_uinst sq [FStar_Syntax_Syntax.U_zero] in
  let uu____6426 =
    let uu____6437 = FStar_Syntax_Syntax.as_arg p in [uu____6437] in
  mk_app uu____6421 uu____6426
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____6448 = head_and_args t in
    match uu____6448 with
    | (head1,args) ->
        let uu____6503 =
          let uu____6518 =
            let uu____6519 = un_uinst head1 in
            uu____6519.FStar_Syntax_Syntax.n in
          (uu____6518, args) in
        (match uu____6503 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____6542)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____6616 =
                    let uu____6621 =
                      let uu____6622 = FStar_Syntax_Syntax.mk_binder b in
                      [uu____6622] in
                    FStar_Syntax_Subst.open_term uu____6621 p in
                  (match uu____6616 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____6653 -> failwith "impossible" in
                       let uu____6658 =
                         let uu____6659 = FStar_Syntax_Free.names p1 in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____6659 in
                       if uu____6658
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____6673 -> FStar_Pervasives_Native.None)
         | uu____6678 -> FStar_Pervasives_Native.None)
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____6713 =
      let uu____6714 = FStar_Syntax_Subst.compress t in
      uu____6714.FStar_Syntax_Syntax.n in
    match uu____6713 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____6829 =
          let uu____6838 =
            let uu____6839 = arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____6839 in
          (b, uu____6838) in
        FStar_Pervasives_Native.Some uu____6829
    | uu____6852 -> FStar_Pervasives_Native.None
let is_free_in:
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun bv  ->
    fun t  ->
      let uu____6865 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____6865
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3
  | QEx of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3
  | BaseConn of (FStar_Ident.lident,FStar_Syntax_Syntax.args)
  FStar_Pervasives_Native.tuple2
let uu___is_QAll: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____6909 -> false
let __proj__QAll__item___0:
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QAll _0 -> _0
let uu___is_QEx: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____6947 -> false
let __proj__QEx__item___0:
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QEx _0 -> _0
let uu___is_BaseConn: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____6983 -> false
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____7018) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____7036) ->
          unmeta_monadic t
      | uu____7055 -> f2 in
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
      let aux f2 uu____7133 =
        match uu____7133 with
        | (lid,arity) ->
            let uu____7142 =
              let uu____7161 = unmeta_monadic f2 in head_and_args uu____7161 in
            (match uu____7142 with
             | (t,args) ->
                 let t1 = un_uinst t in
                 let uu____7195 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity) in
                 if uu____7195
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None) in
      FStar_Util.find_map connectives (aux f1) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____7284 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____7284)
      | uu____7297 ->
          let uu____7298 = FStar_Syntax_Subst.compress t1 in ([], uu____7298) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu____7349 = head_and_args t1 in
        match uu____7349 with
        | (t2,args) ->
            let uu____7408 = un_uinst t2 in
            let uu____7409 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____7444  ->
                      match uu____7444 with
                      | (t3,imp) ->
                          let uu____7455 = unascribe t3 in (uu____7455, imp))) in
            (uu____7408, uu____7409) in
      let rec aux qopt out t1 =
        let uu____7490 = let uu____7507 = flat t1 in (qopt, uu____7507) in
        match uu____7490 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____7534;
                 FStar_Syntax_Syntax.pos = uu____7535;
                 FStar_Syntax_Syntax.vars = uu____7536;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____7539);
                                                             FStar_Syntax_Syntax.tk
                                                               = uu____7540;
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____7541;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____7542;_},uu____7543)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____7642;
                 FStar_Syntax_Syntax.pos = uu____7643;
                 FStar_Syntax_Syntax.vars = uu____7644;_},uu____7645::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____7648);
                  FStar_Syntax_Syntax.tk = uu____7649;
                  FStar_Syntax_Syntax.pos = uu____7650;
                  FStar_Syntax_Syntax.vars = uu____7651;_},uu____7652)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____7766;
               FStar_Syntax_Syntax.pos = uu____7767;
               FStar_Syntax_Syntax.vars = uu____7768;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____7771);
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____7772;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7773;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7774;_},uu____7775)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____7873;
               FStar_Syntax_Syntax.pos = uu____7874;
               FStar_Syntax_Syntax.vars = uu____7875;_},uu____7876::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____7879);
                                                                    FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____7880;
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____7881;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____7882;_},uu____7883)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____7997) ->
            let bs = FStar_List.rev out in
            let uu____8031 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____8031 with
             | (bs1,t2) ->
                 let uu____8040 = patterns t2 in
                 (match uu____8040 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____8112 -> FStar_Pervasives_Native.None in
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
      let uu____8178 = un_squash t in
      FStar_Util.bind_opt uu____8178
        (fun t1  ->
           let uu____8200 = head_and_args' t1 in
           match uu____8200 with
           | (hd1,args) ->
               let uu____8239 =
                 let uu____8244 =
                   let uu____8245 = un_uinst hd1 in
                   uu____8245.FStar_Syntax_Syntax.n in
                 (uu____8244, (FStar_List.length args)) in
               (match uu____8239 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_28) when
                    (_0_28 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_29) when
                    (_0_29 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_30) when
                    (_0_30 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_31) when
                    (_0_31 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_32) when
                    (_0_32 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_33) when
                    (_0_33 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_34) when
                    (_0_34 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_35) when
                    (_0_35 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____8348 -> FStar_Pervasives_Native.None)) in
    let rec destruct_sq_forall t =
      let uu____8371 = un_squash t in
      FStar_Util.bind_opt uu____8371
        (fun t1  ->
           let uu____8392 = arrow_one t1 in
           match uu____8392 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____8407 =
                 let uu____8408 = is_tot_or_gtot_comp c in
                 Prims.op_Negation uu____8408 in
               if uu____8407
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____8417 = comp_to_comp_typ c in
                    uu____8417.FStar_Syntax_Syntax.result_typ in
                  let uu____8418 = FStar_Syntax_Subst.open_term [b] q in
                  match uu____8418 with
                  | (bs,q1) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____8449 -> failwith "impossible" in
                      let uu____8454 =
                        is_free_in (FStar_Pervasives_Native.fst b1) q1 in
                      if uu____8454
                      then
                        let uu____8457 = patterns q1 in
                        (match uu____8457 with
                         | (pats,q2) ->
                             FStar_All.pipe_left maybe_collect
                               (FStar_Pervasives_Native.Some
                                  (QAll ([b1], pats, q2))))
                      else
                        (let uu____8533 =
                           let uu____8534 =
                             let uu____8539 =
                               let uu____8542 =
                                 FStar_Syntax_Syntax.as_arg
                                   (FStar_Pervasives_Native.fst b1).FStar_Syntax_Syntax.sort in
                               let uu____8543 =
                                 let uu____8546 =
                                   FStar_Syntax_Syntax.as_arg q1 in
                                 [uu____8546] in
                               uu____8542 :: uu____8543 in
                             (FStar_Parser_Const.imp_lid, uu____8539) in
                           BaseConn uu____8534 in
                         FStar_Pervasives_Native.Some uu____8533))
           | uu____8549 -> FStar_Pervasives_Native.None)
    and destruct_sq_exists t =
      let uu____8557 = un_squash t in
      FStar_Util.bind_opt uu____8557
        (fun t1  ->
           let uu____8594 = head_and_args' t1 in
           match uu____8594 with
           | (hd1,args) ->
               let uu____8633 =
                 let uu____8648 =
                   let uu____8649 = un_uinst hd1 in
                   uu____8649.FStar_Syntax_Syntax.n in
                 (uu____8648, args) in
               (match uu____8633 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____8668)::(a2,uu____8670)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____8721 =
                      let uu____8722 = FStar_Syntax_Subst.compress a2 in
                      uu____8722.FStar_Syntax_Syntax.n in
                    (match uu____8721 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____8731) ->
                         let uu____8762 = FStar_Syntax_Subst.open_term [b] q in
                         (match uu____8762 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____8801 -> failwith "impossible" in
                              let uu____8806 = patterns q1 in
                              (match uu____8806 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____8881 -> FStar_Pervasives_Native.None)
                | uu____8882 -> FStar_Pervasives_Native.None))
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____8905 = destruct_sq_forall phi in
          (match uu____8905 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_36  -> FStar_Pervasives_Native.Some _0_36)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8927 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____8933 = destruct_sq_exists phi in
          (match uu____8933 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8955 -> f1)
      | uu____8958 -> f1 in
    let phi = unmeta_monadic f in
    let uu____8962 = destruct_base_conn phi in
    FStar_Util.catch_opt uu____8962
      (fun uu____8967  ->
         let uu____8968 = destruct_q_conn phi in
         FStar_Util.catch_opt uu____8968
           (fun uu____8973  ->
              let uu____8974 = destruct_sq_base_conn phi in
              FStar_Util.catch_opt uu____8974
                (fun uu____8979  ->
                   let uu____8980 = destruct_sq_forall phi in
                   FStar_Util.catch_opt uu____8980
                     (fun uu____8985  ->
                        let uu____8986 = destruct_sq_exists phi in
                        FStar_Util.catch_opt uu____8986
                          (fun uu____8990  -> FStar_Pervasives_Native.None)))))
let action_as_lb:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____9000 =
          let uu____9005 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational
              FStar_Pervasives_Native.None in
          FStar_Util.Inr uu____9005 in
        let uu____9006 =
          let uu____9007 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
          arrow a.FStar_Syntax_Syntax.action_params uu____9007 in
        let uu____9012 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None in
        close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____9000
          a.FStar_Syntax_Syntax.action_univs uu____9006
          FStar_Parser_Const.effect_Tot_lid uu____9012 in
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
let mk_reify t =
  let reify_ =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
  let uu____9051 =
    let uu____9056 =
      let uu____9057 =
        let uu____9076 =
          let uu____9079 = FStar_Syntax_Syntax.as_arg t in [uu____9079] in
        (reify_, uu____9076) in
      FStar_Syntax_Syntax.Tm_app uu____9057 in
    FStar_Syntax_Syntax.mk uu____9056 in
  uu____9051 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
let rec delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____9095 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____9125 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____9126 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____9127 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____9156 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____9177 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____9178 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____9179 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____9195) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____9204;
           FStar_Syntax_Syntax.index = uu____9205;
           FStar_Syntax_Syntax.sort = t2;_},uu____9207)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____9221) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____9231,uu____9232) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____9290) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____9319,t2,uu____9321) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____9346,t2) -> delta_qualifier t2
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
  fun t  -> let uu____9378 = delta_qualifier t in incr_delta_depth uu____9378
let is_unknown: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____9383 =
      let uu____9384 = FStar_Syntax_Subst.compress t in
      uu____9384.FStar_Syntax_Syntax.n in
    match uu____9383 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____9389 -> false
let rec list_elements:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____9402 = let uu____9421 = unmeta e in head_and_args uu____9421 in
    match uu____9402 with
    | (head1,args) ->
        let uu____9456 =
          let uu____9471 =
            let uu____9472 = un_uinst head1 in
            uu____9472.FStar_Syntax_Syntax.n in
          (uu____9471, args) in
        (match uu____9456 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9492) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____9516::(hd1,uu____9518)::(tl1,uu____9520)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____9587 =
               let uu____9594 =
                 let uu____9601 = list_elements tl1 in
                 FStar_Util.must uu____9601 in
               hd1 :: uu____9594 in
             FStar_Pervasives_Native.Some uu____9587
         | uu____9618 -> FStar_Pervasives_Native.None)
let rec apply_last f l =
  match l with
  | [] -> failwith "apply_last: got empty list"
  | a::[] -> let uu____9664 = f a in [uu____9664]
  | x::xs -> let uu____9669 = apply_last f xs in x :: uu____9669
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
          let uu____9712 =
            let uu____9717 =
              let uu____9718 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
              FStar_Syntax_Syntax.Tm_fvar uu____9718 in
            FStar_Syntax_Syntax.mk uu____9717 in
          uu____9712 FStar_Pervasives_Native.None rng in
        let cons1 args pos =
          let uu____9734 =
            let uu____9735 =
              let uu____9736 = ctor FStar_Parser_Const.cons_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____9736
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____9735 args in
          uu____9734 FStar_Pervasives_Native.None pos in
        let nil args pos =
          let uu____9750 =
            let uu____9751 =
              let uu____9752 = ctor FStar_Parser_Const.nil_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____9752
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____9751 args in
          uu____9750 FStar_Pervasives_Native.None pos in
        let uu____9755 =
          let uu____9756 =
            let uu____9757 = FStar_Syntax_Syntax.iarg typ in [uu____9757] in
          nil uu____9756 rng in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____9763 =
                 let uu____9764 = FStar_Syntax_Syntax.iarg typ in
                 let uu____9765 =
                   let uu____9768 = FStar_Syntax_Syntax.as_arg t in
                   let uu____9769 =
                     let uu____9772 = FStar_Syntax_Syntax.as_arg a in
                     [uu____9772] in
                   uu____9768 :: uu____9769 in
                 uu____9764 :: uu____9765 in
               cons1 uu____9763 t.FStar_Syntax_Syntax.pos) l uu____9755
let uvar_from_id id t =
  let uu____9792 =
    let uu____9797 =
      let uu____9798 =
        let uu____9819 = FStar_Syntax_Unionfind.from_id id in (uu____9819, t) in
      FStar_Syntax_Syntax.Tm_uvar uu____9798 in
    FStar_Syntax_Syntax.mk uu____9797 in
  uu____9792 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec eqlist eq1 xs ys =
  match (xs, ys) with
  | ([],[]) -> true
  | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
  | uu____9883 -> false
let eqsum e1 e2 x y =
  match (x, y) with
  | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
  | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
  | uu____9986 -> false
let eqprod e1 e2 x y =
  match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
let eqopt e x y =
  match (x, y) with
  | (FStar_Pervasives_Native.Some x1,FStar_Pervasives_Native.Some y1) ->
      e x1 y1
  | uu____10134 -> false
let rec term_eq:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> Prims.bool
  =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_app uu____10285 ->
            let uu____10304 = head_and_args' t in
            (match uu____10304 with
             | (hd1,args) ->
                 let uu___171_10345 = t in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.tk =
                     (uu___171_10345.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___171_10345.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___171_10345.FStar_Syntax_Syntax.vars)
                 })
        | uu____10360 -> t in
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
          x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
          FStar_Syntax_Syntax.bv_eq x y
      | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
          FStar_Syntax_Syntax.fv_eq x y
      | (FStar_Syntax_Syntax.Tm_uinst (t12,us1),FStar_Syntax_Syntax.Tm_uinst
         (t22,us2)) -> (eqlist eq_univs us1 us2) && (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_constant x,FStar_Syntax_Syntax.Tm_constant y)
          -> x = y
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
      | (uu____10713,uu____10714) -> false
and arg_eq:
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
     FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
       FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
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
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      Prims.bool
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
      | (uu____10839,uu____10840) -> false
and eq_flags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list -> Prims.bool
  = fun f1  -> fun f2  -> false
and branch_eq:
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,(FStar_Syntax_Syntax.term',
                                                             FStar_Syntax_Syntax.term')
                                                             FStar_Syntax_Syntax.syntax
                                                             FStar_Pervasives_Native.option,
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,(FStar_Syntax_Syntax.term',
                                                               FStar_Syntax_Syntax.term')
                                                               FStar_Syntax_Syntax.syntax
                                                               FStar_Pervasives_Native.option,
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu____10847  ->
    fun uu____10848  ->
      match (uu____10847, uu____10848) with
      | ((p1,w1,t1),(p2,w2,t2)) -> false
let rec bottom_fold:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f in
      let tn =
        let uu____11028 = FStar_Syntax_Subst.compress t in
        uu____11028.FStar_Syntax_Syntax.n in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____11064 =
              let uu____11083 = ff f1 in
              let uu____11084 =
                FStar_List.map
                  (fun uu____11103  ->
                     match uu____11103 with
                     | (a,q) -> let uu____11114 = ff a in (uu____11114, q))
                  args in
              (uu____11083, uu____11084) in
            FStar_Syntax_Syntax.Tm_app uu____11064
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____11148 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____11148 with
             | (bs1,t') ->
                 let t'' = ff t' in
                 let uu____11156 =
                   let uu____11175 = FStar_Syntax_Subst.close bs1 t'' in
                   (bs1, uu____11175, k) in
                 FStar_Syntax_Syntax.Tm_abs uu____11156)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____11210 = let uu____11219 = ff t1 in (uu____11219, us) in
            FStar_Syntax_Syntax.Tm_uinst uu____11210
        | uu____11220 -> tn in
      f
        (let uu___172_11223 = t in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.tk = (uu___172_11223.FStar_Syntax_Syntax.tk);
           FStar_Syntax_Syntax.pos = (uu___172_11223.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___172_11223.FStar_Syntax_Syntax.vars)
         })
let rec sizeof: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11228 ->
        let uu____11257 =
          let uu____11258 = FStar_Syntax_Subst.compress t in
          sizeof uu____11258 in
        (Prims.parse_int "1") + uu____11257
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____11260 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____11260
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____11262 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____11262
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____11273 = sizeof t1 in (FStar_List.length us) + uu____11273
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____11276) ->
        let uu____11301 = sizeof t1 in
        let uu____11302 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____11313  ->
                 match uu____11313 with
                 | (bv,uu____11319) ->
                     let uu____11320 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu____11320) (Prims.parse_int "0") bs in
        uu____11301 + uu____11302
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____11351 = sizeof hd1 in
        let uu____11352 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____11363  ->
                 match uu____11363 with
                 | (arg,uu____11369) ->
                     let uu____11370 = sizeof arg in acc + uu____11370)
            (Prims.parse_int "0") args in
        uu____11351 + uu____11352
    | uu____11371 -> Prims.parse_int "1"
let is_synth_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____11376 =
      let uu____11377 = un_uinst t in uu____11377.FStar_Syntax_Syntax.n in
    match uu____11376 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
    | uu____11383 -> false
let mk_alien b s r =
  let uu____11409 =
    let uu____11414 =
      let uu____11415 =
        let uu____11424 =
          let uu____11425 =
            let uu____11430 = FStar_Dyn.mkdyn b in (uu____11430, s) in
          FStar_Syntax_Syntax.Meta_alien uu____11425 in
        (FStar_Syntax_Syntax.tun, uu____11424) in
      FStar_Syntax_Syntax.Tm_meta uu____11415 in
    FStar_Syntax_Syntax.mk uu____11414 in
  uu____11409 FStar_Pervasives_Native.None
    (match r with
     | FStar_Pervasives_Native.Some r1 -> r1
     | FStar_Pervasives_Native.None  -> FStar_Range.dummyRange)
let un_alien: FStar_Syntax_Syntax.term -> FStar_Dyn.dyn =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        (uu____11445,FStar_Syntax_Syntax.Meta_alien (blob,uu____11447)) ->
        blob
    | uu____11456 -> failwith "Something paranormal occurred"