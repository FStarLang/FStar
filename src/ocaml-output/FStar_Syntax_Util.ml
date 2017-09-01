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
let arg_of_non_null_binder:
  'Auu____23 .
    (FStar_Syntax_Syntax.bv,'Auu____23) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term,'Auu____23) FStar_Pervasives_Native.tuple2
  =
  fun uu____35  ->
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
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
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
let name_function_binders:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____312 =
          let uu____315 =
            let uu____316 =
              let uu____329 = name_binders binders in (uu____329, comp) in
            FStar_Syntax_Syntax.Tm_arrow uu____316 in
          FStar_Syntax_Syntax.mk uu____315 in
        uu____312 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____347 -> t
let null_binders_of_tks:
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____388  ->
            match uu____388 with
            | (t,imp) ->
                let uu____399 =
                  let uu____400 = FStar_Syntax_Syntax.null_binder t in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____400 in
                (uu____399, imp)))
let binders_of_tks:
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____451  ->
            match uu____451 with
            | (t,imp) ->
                let uu____468 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t in
                (uu____468, imp)))
let binders_of_freevars:
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list
  =
  fun fvs  ->
    let uu____479 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____479
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
let mk_subst: 'Auu____490 . 'Auu____490 -> 'Auu____490 Prims.list =
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
          (fun uu____581  ->
             fun uu____582  ->
               match (uu____581, uu____582) with
               | ((x,uu____600),(y,uu____602)) ->
                   let uu____611 =
                     let uu____618 = FStar_Syntax_Syntax.bv_to_name y in
                     (x, uu____618) in
                   FStar_Syntax_Syntax.NT uu____611) replace_xs with_ys
      else failwith "Ill-formed substitution"
let rec unmeta: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____626) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____632,uu____633) -> unmeta e2
    | uu____674 -> e1
let rec univ_kernel:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____687 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____688 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____698 = univ_kernel u1 in
        (match uu____698 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____709 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____716 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let constant_univ_as_nat: FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  ->
    let uu____725 = univ_kernel u in FStar_Pervasives_Native.snd uu____725
let rec compare_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____738,uu____739) ->
          failwith "Impossible: compare_univs"
      | (uu____740,FStar_Syntax_Syntax.U_bvar uu____741) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_unknown ,uu____742) -> - (Prims.parse_int "1")
      | (uu____743,FStar_Syntax_Syntax.U_unknown ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_zero ,uu____744) -> - (Prims.parse_int "1")
      | (uu____745,FStar_Syntax_Syntax.U_zero ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____748,FStar_Syntax_Syntax.U_unif
         uu____749) -> - (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____758,FStar_Syntax_Syntax.U_name
         uu____759) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____786 = FStar_Syntax_Unionfind.univ_uvar_id u11 in
          let uu____787 = FStar_Syntax_Unionfind.univ_uvar_id u21 in
          uu____786 - uu____787
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1 in
          let n2 = FStar_List.length us2 in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____818 = FStar_List.zip us1 us2 in
               FStar_Util.find_map uu____818
                 (fun uu____833  ->
                    match uu____833 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21 in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None) in
             match copt with
             | FStar_Pervasives_Native.None  -> Prims.parse_int "0"
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____847,uu____848) ->
          - (Prims.parse_int "1")
      | (uu____851,FStar_Syntax_Syntax.U_max uu____852) ->
          Prims.parse_int "1"
      | uu____855 ->
          let uu____860 = univ_kernel u1 in
          (match uu____860 with
           | (k1,n1) ->
               let uu____867 = univ_kernel u2 in
               (match uu____867 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2 in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
let eq_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____884 = compare_univs u1 u2 in
      uu____884 = (Prims.parse_int "0")
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
    | FStar_Syntax_Syntax.Total uu____912 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____921 ->
        FStar_Parser_Const.effect_GTot_lid
let comp_flags:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____942 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____951 ->
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
            let uu____990 =
              let uu____991 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____991 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____990;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
        | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
            let uu____1018 =
              let uu____1019 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____1019 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____1018;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            } in
      let uu___163_1036 = c in
      let uu____1037 =
        let uu____1038 =
          let uu___164_1039 = comp_to_comp_typ c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___164_1039.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___164_1039.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___164_1039.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___164_1039.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu____1038 in
      {
        FStar_Syntax_Syntax.n = uu____1037;
        FStar_Syntax_Syntax.pos = (uu___163_1036.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___163_1036.FStar_Syntax_Syntax.vars)
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
    | uu____1073 ->
        failwith "Assertion failed: Computation type without universe"
let is_named_tot:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1083 -> true
    | FStar_Syntax_Syntax.GTotal uu____1092 -> false
let is_total_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___151_1112  ->
               match uu___151_1112 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1113 -> false)))
let is_total_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___152_1121  ->
               match uu___152_1121 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1122 -> false)))
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
            (fun uu___153_1130  ->
               match uu___153_1130 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1131 -> false)))
let is_partial_return:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___154_1143  ->
            match uu___154_1143 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1144 -> false))
let is_lcomp_partial_return: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___155_1152  ->
            match uu___155_1152 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1153 -> false))
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
    | FStar_Syntax_Syntax.Total uu____1174 -> true
    | FStar_Syntax_Syntax.GTotal uu____1183 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___156_1196  ->
                   match uu___156_1196 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1197 -> false)))
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
            (fun uu___157_1217  ->
               match uu___157_1217 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1218 -> false)))
let is_pure_or_ghost_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
let is_pure_or_ghost_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1227 =
      let uu____1228 = FStar_Syntax_Subst.compress t in
      uu____1228.FStar_Syntax_Syntax.n in
    match uu____1227 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1231,c) -> is_pure_or_ghost_comp c
    | uu____1249 -> true
let is_lemma_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1259 -> false
let is_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1264 =
      let uu____1265 = FStar_Syntax_Subst.compress t in
      uu____1265.FStar_Syntax_Syntax.n in
    match uu____1264 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1268,c) -> is_lemma_comp c
    | uu____1286 -> false
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
    | uu____1352 -> (t1, [])
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
        let uu____1418 = head_and_args' head1 in
        (match uu____1418 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1475 -> (t1, [])
let un_uinst: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1496) ->
        FStar_Syntax_Subst.compress t2
    | uu____1501 -> t1
let is_smt_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1506 =
      let uu____1507 = FStar_Syntax_Subst.compress t in
      uu____1507.FStar_Syntax_Syntax.n in
    match uu____1506 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1510,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1532)::uu____1533 ->
                  let pats' = unmeta pats in
                  let uu____1577 = head_and_args pats' in
                  (match uu____1577 with
                   | (head1,uu____1593) ->
                       let uu____1614 =
                         let uu____1615 = un_uinst head1 in
                         uu____1615.FStar_Syntax_Syntax.n in
                       (match uu____1614 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1619 -> false))
              | uu____1620 -> false)
         | uu____1629 -> false)
    | uu____1630 -> false
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
                (fun uu___158_1643  ->
                   match uu___158_1643 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1644 -> false)))
    | uu____1645 -> false
let comp_result:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1659) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1669) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let set_result_typ:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____1691 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____1700 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___165_1712 = ct in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___165_1712.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___165_1712.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___165_1712.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___165_1712.FStar_Syntax_Syntax.flags)
             })
let is_trivial_wp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___159_1724  ->
            match uu___159_1724 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____1725 -> false))
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
    | uu____1743 -> false
let rec unascribe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1750,uu____1751) ->
        unascribe e2
    | uu____1792 -> e1
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1842,uu____1843) ->
          ascribe t' k
      | uu____1884 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
type eq_result =
  | Equal
  | NotEqual
  | Unknown
let uu___is_Equal: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1909 -> false
let uu___is_NotEqual: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1914 -> false
let uu___is_Unknown: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1919 -> false
let rec eq_tm:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        let uu____1940 =
          let uu____1953 = unascribe t in head_and_args' uu____1953 in
        match uu____1940 with
        | (hd1,args) ->
            FStar_Syntax_Syntax.mk_Tm_app hd1 args
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
      let equal_if uu___160_1983 = if uu___160_1983 then Equal else Unknown in
      let equal_iff uu___161_1988 = if uu___161_1988 then Equal else NotEqual in
      let eq_and f g = match f with | Equal  -> g () | uu____2002 -> Unknown in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2010) -> NotEqual
        | (uu____2011,NotEqual ) -> NotEqual
        | (Unknown ,uu____2012) -> Unknown
        | (uu____2013,Unknown ) -> Unknown in
      let equal_data f1 args1 f2 args2 =
        let uu____2051 = FStar_Syntax_Syntax.fv_eq f1 f2 in
        if uu____2051
        then
          let uu____2055 = FStar_List.zip args1 args2 in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2113  ->
                    match uu____2113 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2141 = eq_tm a1 a2 in eq_inj acc uu____2141)
               Equal) uu____2055
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
            (let uu____2160 = FStar_Syntax_Syntax.fv_eq f g in
             equal_if uu____2160)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2173 = eq_tm f g in
          eq_and uu____2173
            (fun uu____2176  ->
               let uu____2177 = eq_univs_list us vs in equal_if uu____2177)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2180 = FStar_Const.eq_const c d in equal_iff uu____2180
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2182),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2184)) ->
          let uu____2233 = FStar_Syntax_Unionfind.equiv u1 u2 in
          equal_if uu____2233
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2278 =
            let uu____2283 =
              let uu____2284 = un_uinst h1 in
              uu____2284.FStar_Syntax_Syntax.n in
            let uu____2287 =
              let uu____2288 = un_uinst h2 in
              uu____2288.FStar_Syntax_Syntax.n in
            (uu____2283, uu____2287) in
          (match uu____2278 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (f1.FStar_Syntax_Syntax.fv_qual =
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
                 &&
                 (f2.FStar_Syntax_Syntax.fv_qual =
                    (FStar_Pervasives_Native.Some
                       FStar_Syntax_Syntax.Data_ctor))
               -> equal_data f1 args1 f2 args2
           | uu____2297 ->
               let uu____2302 = eq_tm h1 h2 in
               eq_and uu____2302 (fun uu____2304  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____2307 = eq_univs u v1 in equal_if uu____2307
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____2309),uu____2310) ->
          eq_tm t12 t21
      | (uu____2315,FStar_Syntax_Syntax.Tm_meta (t22,uu____2317)) ->
          eq_tm t11 t22
      | uu____2322 -> Unknown
and eq_args:
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____2358)::a11,(b,uu____2361)::b1) ->
          let uu____2415 = eq_tm a b in
          (match uu____2415 with
           | Equal  -> eq_args a11 b1
           | uu____2416 -> Unknown)
      | uu____2417 -> Unknown
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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____2430) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2436,uu____2437) ->
        unrefine t2
    | uu____2478 -> t1
let rec is_unit: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2483 =
      let uu____2484 = unrefine t in uu____2484.FStar_Syntax_Syntax.n in
    match uu____2483 with
    | FStar_Syntax_Syntax.Tm_type uu____2487 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2490) -> is_unit t1
    | uu____2495 -> false
let rec non_informative: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2500 =
      let uu____2501 = unrefine t in uu____2501.FStar_Syntax_Syntax.n in
    match uu____2500 with
    | FStar_Syntax_Syntax.Tm_type uu____2504 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____2507) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2529) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____2534,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____2552 -> false
let is_fun: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____2557 =
      let uu____2558 = FStar_Syntax_Subst.compress e in
      uu____2558.FStar_Syntax_Syntax.n in
    match uu____2557 with
    | FStar_Syntax_Syntax.Tm_abs uu____2561 -> true
    | uu____2578 -> false
let is_function_typ: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2583 =
      let uu____2584 = FStar_Syntax_Subst.compress t in
      uu____2584.FStar_Syntax_Syntax.n in
    match uu____2583 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2587 -> true
    | uu____2600 -> false
let rec pre_typ: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____2607) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2613,uu____2614) ->
        pre_typ t2
    | uu____2655 -> t1
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
      let uu____2675 =
        let uu____2676 = un_uinst typ1 in uu____2676.FStar_Syntax_Syntax.n in
      match uu____2675 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1 in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____2731 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____2755 -> FStar_Pervasives_Native.None
let lids_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____2772,lids) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____2778,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2789,uu____2790,uu____2791,uu____2792,uu____2793) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____2803,uu____2804,uu____2805,uu____2806) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____2812,uu____2813,uu____2814,uu____2815,uu____2816) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2822,uu____2823) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2825,uu____2826) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____2829 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____2830 -> []
    | FStar_Syntax_Syntax.Sig_main uu____2831 -> []
let lid_of_sigelt:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____2843 -> FStar_Pervasives_Native.None
let quals_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals
let range_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng
let range_of_lb:
  'Auu____2862 'Auu____2863 .
    ((FStar_Syntax_Syntax.bv,FStar_Ident.lid) FStar_Util.either,'Auu____2863,
      'Auu____2862) FStar_Pervasives_Native.tuple3 -> FStar_Range.range
  =
  fun uu___162_2877  ->
    match uu___162_2877 with
    | (FStar_Util.Inl x,uu____2889,uu____2890) ->
        FStar_Syntax_Syntax.range_of_bv x
    | (FStar_Util.Inr l,uu____2896,uu____2897) -> FStar_Ident.range_of_lid l
let range_of_arg:
  'Auu____2908 'Auu____2909 .
    ('Auu____2909 FStar_Syntax_Syntax.syntax,'Auu____2908)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____2919  ->
    match uu____2919 with | (hd1,uu____2927) -> hd1.FStar_Syntax_Syntax.pos
let range_of_args:
  'Auu____2940 'Auu____2941 .
    ('Auu____2941 FStar_Syntax_Syntax.syntax,'Auu____2940)
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
          let uu____3065 =
            let uu____3068 =
              let uu____3069 =
                let uu____3076 =
                  FStar_Syntax_Syntax.fvar l
                    FStar_Syntax_Syntax.Delta_constant
                    (FStar_Pervasives_Native.Some
                       FStar_Syntax_Syntax.Data_ctor) in
                (uu____3076,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Data_app)) in
              FStar_Syntax_Syntax.Tm_meta uu____3069 in
            FStar_Syntax_Syntax.mk uu____3068 in
          uu____3065 FStar_Pervasives_Native.None
            (FStar_Ident.range_of_lid l)
      | uu____3080 ->
          let e =
            let uu____3092 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            mk_app uu____3092 args in
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
      let uu____3105 =
        let uu____3110 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9") in
        (uu____3110, (x.FStar_Ident.idRange)) in
      FStar_Ident.mk_ident uu____3105
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
          let uu____3153 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____3153
          then
            let uu____3154 =
              let uu____3159 =
                let uu____3160 = FStar_Util.string_of_int i in
                Prims.strcat "_" uu____3160 in
              let uu____3161 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____3159, uu____3161) in
            FStar_Ident.mk_ident uu____3154
          else x.FStar_Syntax_Syntax.ppname in
        let y =
          let uu___166_3164 = x in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___166_3164.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___166_3164.FStar_Syntax_Syntax.sort)
          } in
        let uu____3165 = mk_field_projector_name_from_ident lid nm in
        (uu____3165, y)
let set_uvar:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun uv  ->
    fun t  ->
      let uu____3174 = FStar_Syntax_Unionfind.find uv in
      match uu____3174 with
      | FStar_Pervasives_Native.Some uu____3177 ->
          let uu____3178 =
            let uu____3179 =
              let uu____3180 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu____3180 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3179 in
          failwith uu____3178
      | uu____3181 -> FStar_Syntax_Unionfind.change uv t
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
      | uu____3254 -> q1 = q2
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
              let uu____3288 =
                let uu___167_3289 = rc in
                let uu____3290 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs) in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___167_3289.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____3290;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___167_3289.FStar_Syntax_Syntax.residual_flags)
                } in
              FStar_Pervasives_Native.Some uu____3288 in
        match bs with
        | [] -> t
        | uu____3301 ->
            let body =
              let uu____3303 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____3303 in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____3331 =
                   let uu____3334 =
                     let uu____3335 =
                       let uu____3352 =
                         let uu____3359 = FStar_Syntax_Subst.close_binders bs in
                         FStar_List.append uu____3359 bs' in
                       let uu____3370 = close_lopt lopt' in
                       (uu____3352, t1, uu____3370) in
                     FStar_Syntax_Syntax.Tm_abs uu____3335 in
                   FStar_Syntax_Syntax.mk uu____3334 in
                 uu____3331 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____3386 ->
                 let uu____3393 =
                   let uu____3396 =
                     let uu____3397 =
                       let uu____3414 = FStar_Syntax_Subst.close_binders bs in
                       let uu____3415 = close_lopt lopt in
                       (uu____3414, body, uu____3415) in
                     FStar_Syntax_Syntax.Tm_abs uu____3397 in
                   FStar_Syntax_Syntax.mk uu____3396 in
                 uu____3393 FStar_Pervasives_Native.None
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
      | uu____3455 ->
          let uu____3462 =
            let uu____3465 =
              let uu____3466 =
                let uu____3479 = FStar_Syntax_Subst.close_binders bs in
                let uu____3480 = FStar_Syntax_Subst.close_comp bs c in
                (uu____3479, uu____3480) in
              FStar_Syntax_Syntax.Tm_arrow uu____3466 in
            FStar_Syntax_Syntax.mk uu____3465 in
          uu____3462 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
let flat_arrow:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c in
      let uu____3513 =
        let uu____3514 = FStar_Syntax_Subst.compress t in
        uu____3514.FStar_Syntax_Syntax.n in
      match uu____3513 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____3540) ->
               let uu____3549 =
                 let uu____3550 = FStar_Syntax_Subst.compress tres in
                 uu____3550.FStar_Syntax_Syntax.n in
               (match uu____3549 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____3585 -> t)
           | uu____3586 -> t)
      | uu____3587 -> t
let refine:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____3598 =
        let uu____3599 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____3599 t.FStar_Syntax_Syntax.pos in
      let uu____3600 =
        let uu____3603 =
          let uu____3604 =
            let uu____3611 =
              let uu____3612 =
                let uu____3613 = FStar_Syntax_Syntax.mk_binder b in
                [uu____3613] in
              FStar_Syntax_Subst.close uu____3612 t in
            (b, uu____3611) in
          FStar_Syntax_Syntax.Tm_refine uu____3604 in
        FStar_Syntax_Syntax.mk uu____3603 in
      uu____3600 FStar_Pervasives_Native.None uu____3598
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
        let uu____3664 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____3664 with
         | (bs1,c1) ->
             let uu____3681 = is_tot_or_gtot_comp c1 in
             if uu____3681
             then
               let uu____3692 = arrow_formals_comp (comp_result c1) in
               (match uu____3692 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____3738 ->
        let uu____3739 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3739)
let rec arrow_formals:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let uu____3766 = arrow_formals_comp k in
    match uu____3766 with | (bs,c) -> (bs, (comp_result c))
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
          let uu____3843 =
            let uu___168_3844 = rc in
            let uu____3845 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___168_3844.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____3845;
              FStar_Syntax_Syntax.residual_flags =
                (uu___168_3844.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____3843
      | uu____3852 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____3880 =
        let uu____3881 =
          let uu____3884 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____3884 in
        uu____3881.FStar_Syntax_Syntax.n in
      match uu____3880 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____3922 = aux t2 what in
          (match uu____3922 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____3982 -> ([], t1, abs_body_lcomp) in
    let uu____3995 = aux t FStar_Pervasives_Native.None in
    match uu____3995 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____4037 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____4037 with
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
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.letbinding
  =
  fun lbname  ->
    fun univ_vars  ->
      fun typ  ->
        fun eff  ->
          fun def  ->
            let typ1 = FStar_Syntax_Subst.close_univ_vars univ_vars typ in
            let def1 = FStar_Syntax_Subst.close_univ_vars univ_vars def in
            mk_letbinding lbname univ_vars typ1 eff def1
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
            let uu____4182 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____4182 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____4211 ->
            let t' = arrow binders c in
            let uu____4221 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____4221 with
             | (uvs1,t'1) ->
                 let uu____4240 =
                   let uu____4241 = FStar_Syntax_Subst.compress t'1 in
                   uu____4241.FStar_Syntax_Syntax.n in
                 (match uu____4240 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____4282 -> failwith "Impossible"))
let is_tuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____4300 -> false
let is_dtuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____4306 -> false
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
      let uu____4346 =
        let uu____4347 = pre_typ t in uu____4347.FStar_Syntax_Syntax.n in
      match uu____4346 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____4351 -> false
let rec is_constructed_typ:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____4360 =
        let uu____4361 = pre_typ t in uu____4361.FStar_Syntax_Syntax.n in
      match uu____4360 with
      | FStar_Syntax_Syntax.Tm_fvar uu____4364 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____4366) ->
          is_constructed_typ t1 lid
      | uu____4387 -> false
let rec get_tycon:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____4397 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____4398 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____4399 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____4401) -> get_tycon t2
    | uu____4422 -> FStar_Pervasives_Native.None
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
    let uu____4434 =
      let uu____4435 = un_uinst t in uu____4435.FStar_Syntax_Syntax.n in
    match uu____4434 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Parser_Const.fstar_refl_embed_lid
    | uu____4439 -> false
let is_fstar_tactics_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4444 =
      let uu____4445 = un_uinst t in uu____4445.FStar_Syntax_Syntax.n in
    match uu____4444 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____4449 -> false
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
  fun uu____4461  ->
    let u =
      let uu____4467 = FStar_Syntax_Unionfind.univ_fresh () in
      FStar_All.pipe_left (fun _0_28  -> FStar_Syntax_Syntax.U_unif _0_28)
        uu____4467 in
    let uu____4484 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange in
    (uu____4484, u)
let attr_substitute: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant
       (FStar_Const.Const_string
          ((FStar_Util.bytes_of_string "substitute"), FStar_Range.dummyRange)))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
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
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu____4540 =
            let uu____4543 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            let uu____4544 =
              let uu____4547 =
                let uu____4548 =
                  let uu____4563 =
                    let uu____4566 = FStar_Syntax_Syntax.as_arg phi11 in
                    let uu____4567 =
                      let uu____4570 = FStar_Syntax_Syntax.as_arg phi2 in
                      [uu____4570] in
                    uu____4566 :: uu____4567 in
                  (tand, uu____4563) in
                FStar_Syntax_Syntax.Tm_app uu____4548 in
              FStar_Syntax_Syntax.mk uu____4547 in
            uu____4544 FStar_Pervasives_Native.None uu____4543 in
          FStar_Pervasives_Native.Some uu____4540
let mk_binop:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____4596 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos in
        let uu____4597 =
          let uu____4600 =
            let uu____4601 =
              let uu____4616 =
                let uu____4619 = FStar_Syntax_Syntax.as_arg phi1 in
                let uu____4620 =
                  let uu____4623 = FStar_Syntax_Syntax.as_arg phi2 in
                  [uu____4623] in
                uu____4619 :: uu____4620 in
              (op_t, uu____4616) in
            FStar_Syntax_Syntax.Tm_app uu____4601 in
          FStar_Syntax_Syntax.mk uu____4600 in
        uu____4597 FStar_Pervasives_Native.None uu____4596
let mk_neg:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun phi  ->
    let uu____4637 =
      let uu____4640 =
        let uu____4641 =
          let uu____4656 =
            let uu____4659 = FStar_Syntax_Syntax.as_arg phi in [uu____4659] in
          (t_not, uu____4656) in
        FStar_Syntax_Syntax.Tm_app uu____4641 in
      FStar_Syntax_Syntax.mk uu____4640 in
    uu____4637 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
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
    let uu____4731 =
      let uu____4734 =
        let uu____4735 =
          let uu____4750 =
            let uu____4753 = FStar_Syntax_Syntax.as_arg e in [uu____4753] in
          (b2t_v, uu____4750) in
        FStar_Syntax_Syntax.Tm_app uu____4735 in
      FStar_Syntax_Syntax.mk uu____4734 in
    uu____4731 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
let teq: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.eq2_lid
let mk_untyped_eq2:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun e1  ->
    fun e2  ->
      let uu____4769 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos in
      let uu____4770 =
        let uu____4773 =
          let uu____4774 =
            let uu____4789 =
              let uu____4792 = FStar_Syntax_Syntax.as_arg e1 in
              let uu____4793 =
                let uu____4796 = FStar_Syntax_Syntax.as_arg e2 in
                [uu____4796] in
              uu____4792 :: uu____4793 in
            (teq, uu____4789) in
          FStar_Syntax_Syntax.Tm_app uu____4774 in
        FStar_Syntax_Syntax.mk uu____4773 in
      uu____4770 FStar_Pervasives_Native.None uu____4769
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
          let uu____4819 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          let uu____4820 =
            let uu____4823 =
              let uu____4824 =
                let uu____4839 =
                  let uu____4842 = FStar_Syntax_Syntax.iarg t in
                  let uu____4843 =
                    let uu____4846 = FStar_Syntax_Syntax.as_arg e1 in
                    let uu____4847 =
                      let uu____4850 = FStar_Syntax_Syntax.as_arg e2 in
                      [uu____4850] in
                    uu____4846 :: uu____4847 in
                  uu____4842 :: uu____4843 in
                (eq_inst, uu____4839) in
              FStar_Syntax_Syntax.Tm_app uu____4824 in
            FStar_Syntax_Syntax.mk uu____4823 in
          uu____4820 FStar_Pervasives_Native.None uu____4819
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
        let uu____4876 =
          let uu____4879 =
            let uu____4880 =
              let uu____4895 =
                let uu____4898 = FStar_Syntax_Syntax.iarg t in
                let uu____4899 =
                  let uu____4902 = FStar_Syntax_Syntax.as_arg x in
                  let uu____4903 =
                    let uu____4906 = FStar_Syntax_Syntax.as_arg t' in
                    [uu____4906] in
                  uu____4902 :: uu____4903 in
                uu____4898 :: uu____4899 in
              (t_has_type1, uu____4895) in
            FStar_Syntax_Syntax.Tm_app uu____4880 in
          FStar_Syntax_Syntax.mk uu____4879 in
        uu____4876 FStar_Pervasives_Native.None FStar_Range.dummyRange
let lex_t: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.lex_t_lid
let lex_top: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  let uu____4916 =
    let uu____4919 =
      let uu____4920 =
        let uu____4927 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
        (uu____4927, [FStar_Syntax_Syntax.U_zero]) in
      FStar_Syntax_Syntax.Tm_uinst uu____4920 in
    FStar_Syntax_Syntax.mk uu____4919 in
  uu____4916 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
    let uu____4941 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____4954 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____4965 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags)) in
    match uu____4941 with
    | (eff_name,flags) ->
        {
          FStar_Syntax_Syntax.eff_name = eff_name;
          FStar_Syntax_Syntax.res_typ = (comp_result c0);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = ((fun uu____4986  -> c0))
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
        let uu____5051 =
          let uu____5054 =
            let uu____5055 =
              let uu____5070 =
                let uu____5073 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
                let uu____5074 =
                  let uu____5077 =
                    let uu____5078 =
                      let uu____5079 =
                        let uu____5080 = FStar_Syntax_Syntax.mk_binder x in
                        [uu____5080] in
                      abs uu____5079 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0)) in
                    FStar_Syntax_Syntax.as_arg uu____5078 in
                  [uu____5077] in
                uu____5073 :: uu____5074 in
              (fa, uu____5070) in
            FStar_Syntax_Syntax.Tm_app uu____5055 in
          FStar_Syntax_Syntax.mk uu____5054 in
        uu____5051 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
             let uu____5126 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____5126
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
let rec is_wild_pat:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____5136 -> true
    | uu____5137 -> false
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
          let uu____5179 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos in
          (uu____5179, FStar_Pervasives_Native.None, t1) in
        let else_branch =
          let uu____5207 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos in
          (uu____5207, FStar_Pervasives_Native.None, t2) in
        let uu____5220 =
          let uu____5221 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____5221 in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____5220
let mk_squash:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun p  ->
    let sq =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
        (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
        FStar_Pervasives_Native.None in
    let uu____5289 =
      FStar_Syntax_Syntax.mk_Tm_uinst sq [FStar_Syntax_Syntax.U_zero] in
    let uu____5292 =
      let uu____5301 = FStar_Syntax_Syntax.as_arg p in [uu____5301] in
    mk_app uu____5289 uu____5292
let un_squash:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____5310 = head_and_args t in
    match uu____5310 with
    | (head1,args) ->
        let uu____5351 =
          let uu____5364 =
            let uu____5365 = un_uinst head1 in
            uu____5365.FStar_Syntax_Syntax.n in
          (uu____5364, args) in
        (match uu____5351 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____5382)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____5434 =
                    let uu____5439 =
                      let uu____5440 = FStar_Syntax_Syntax.mk_binder b in
                      [uu____5440] in
                    FStar_Syntax_Subst.open_term uu____5439 p in
                  (match uu____5434 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____5469 -> failwith "impossible" in
                       let uu____5474 =
                         let uu____5475 = FStar_Syntax_Free.names p1 in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____5475 in
                       if uu____5474
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____5485 -> FStar_Pervasives_Native.None)
         | uu____5488 -> FStar_Pervasives_Native.None)
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____5519 =
      let uu____5520 = FStar_Syntax_Subst.compress t in
      uu____5520.FStar_Syntax_Syntax.n in
    match uu____5519 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____5617 =
          let uu____5626 =
            let uu____5627 = arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____5627 in
          (b, uu____5626) in
        FStar_Pervasives_Native.Some uu____5617
    | uu____5640 -> FStar_Pervasives_Native.None
let is_free_in:
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun bv  ->
    fun t  ->
      let uu____5653 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____5653
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
    match projectee with | QAll _0 -> true | uu____5697 -> false
let __proj__QAll__item___0:
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QAll _0 -> _0
let uu___is_QEx: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____5735 -> false
let __proj__QEx__item___0:
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QEx _0 -> _0
let uu___is_BaseConn: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____5771 -> false
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____5806) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____5818) ->
          unmeta_monadic t
      | uu____5831 -> f2 in
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
      let aux f2 uu____5909 =
        match uu____5909 with
        | (lid,arity) ->
            let uu____5918 =
              let uu____5933 = unmeta_monadic f2 in head_and_args uu____5933 in
            (match uu____5918 with
             | (t,args) ->
                 let t1 = un_uinst t in
                 let uu____5959 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity) in
                 if uu____5959
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None) in
      FStar_Util.find_map connectives (aux f1) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____6034 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____6034)
      | uu____6045 ->
          let uu____6046 = FStar_Syntax_Subst.compress t1 in ([], uu____6046) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu____6093 = head_and_args t1 in
        match uu____6093 with
        | (t2,args) ->
            let uu____6140 = un_uinst t2 in
            let uu____6141 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6174  ->
                      match uu____6174 with
                      | (t3,imp) ->
                          let uu____6185 = unascribe t3 in (uu____6185, imp))) in
            (uu____6140, uu____6141) in
      let rec aux qopt out t1 =
        let uu____6220 = let uu____6237 = flat t1 in (qopt, uu____6237) in
        match uu____6220 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____6264;
                 FStar_Syntax_Syntax.vars = uu____6265;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____6268);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____6269;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____6270;_},uu____6271)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____6348;
                 FStar_Syntax_Syntax.vars = uu____6349;_},uu____6350::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____6353);
                  FStar_Syntax_Syntax.pos = uu____6354;
                  FStar_Syntax_Syntax.vars = uu____6355;_},uu____6356)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____6444;
               FStar_Syntax_Syntax.vars = uu____6445;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____6448);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6449;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6450;_},uu____6451)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____6527;
               FStar_Syntax_Syntax.vars = uu____6528;_},uu____6529::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____6532);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6533;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____6534;_},uu____6535)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____6623) ->
            let bs = FStar_List.rev out in
            let uu____6657 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____6657 with
             | (bs1,t2) ->
                 let uu____6666 = patterns t2 in
                 (match uu____6666 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____6728 -> FStar_Pervasives_Native.None in
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
      let uu____6794 = un_squash t in
      FStar_Util.bind_opt uu____6794
        (fun t1  ->
           let uu____6810 = head_and_args' t1 in
           match uu____6810 with
           | (hd1,args) ->
               let uu____6843 =
                 let uu____6848 =
                   let uu____6849 = un_uinst hd1 in
                   uu____6849.FStar_Syntax_Syntax.n in
                 (uu____6848, (FStar_List.length args)) in
               (match uu____6843 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_29) when
                    (_0_29 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_30) when
                    (_0_30 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_31) when
                    (_0_31 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_32) when
                    (_0_32 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_33) when
                    (_0_33 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_34) when
                    (_0_34 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_35) when
                    (_0_35 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_36) when
                    (_0_36 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____6932 -> FStar_Pervasives_Native.None)) in
    let rec destruct_sq_forall t =
      let uu____6955 = un_squash t in
      FStar_Util.bind_opt uu____6955
        (fun t1  ->
           let uu____6970 = arrow_one t1 in
           match uu____6970 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____6985 =
                 let uu____6986 = is_tot_or_gtot_comp c in
                 Prims.op_Negation uu____6986 in
               if uu____6985
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____6993 = comp_to_comp_typ c in
                    uu____6993.FStar_Syntax_Syntax.result_typ in
                  let uu____6994 = FStar_Syntax_Subst.open_term [b] q in
                  match uu____6994 with
                  | (bs,q1) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____7025 -> failwith "impossible" in
                      let uu____7030 =
                        is_free_in (FStar_Pervasives_Native.fst b1) q1 in
                      if uu____7030
                      then
                        let uu____7033 = patterns q1 in
                        (match uu____7033 with
                         | (pats,q2) ->
                             FStar_All.pipe_left maybe_collect
                               (FStar_Pervasives_Native.Some
                                  (QAll ([b1], pats, q2))))
                      else
                        (let uu____7101 =
                           let uu____7102 =
                             let uu____7107 =
                               let uu____7110 =
                                 FStar_Syntax_Syntax.as_arg
                                   (FStar_Pervasives_Native.fst b1).FStar_Syntax_Syntax.sort in
                               let uu____7111 =
                                 let uu____7114 =
                                   FStar_Syntax_Syntax.as_arg q1 in
                                 [uu____7114] in
                               uu____7110 :: uu____7111 in
                             (FStar_Parser_Const.imp_lid, uu____7107) in
                           BaseConn uu____7102 in
                         FStar_Pervasives_Native.Some uu____7101))
           | uu____7117 -> FStar_Pervasives_Native.None)
    and destruct_sq_exists t =
      let uu____7125 = un_squash t in
      FStar_Util.bind_opt uu____7125
        (fun t1  ->
           let uu____7156 = head_and_args' t1 in
           match uu____7156 with
           | (hd1,args) ->
               let uu____7189 =
                 let uu____7202 =
                   let uu____7203 = un_uinst hd1 in
                   uu____7203.FStar_Syntax_Syntax.n in
                 (uu____7202, args) in
               (match uu____7189 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____7218)::(a2,uu____7220)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____7255 =
                      let uu____7256 = FStar_Syntax_Subst.compress a2 in
                      uu____7256.FStar_Syntax_Syntax.n in
                    (match uu____7255 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____7263) ->
                         let uu____7290 = FStar_Syntax_Subst.open_term [b] q in
                         (match uu____7290 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____7329 -> failwith "impossible" in
                              let uu____7334 = patterns q1 in
                              (match uu____7334 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____7401 -> FStar_Pervasives_Native.None)
                | uu____7402 -> FStar_Pervasives_Native.None))
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____7423 = destruct_sq_forall phi in
          (match uu____7423 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____7445 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____7451 = destruct_sq_exists phi in
          (match uu____7451 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____7473 -> f1)
      | uu____7476 -> f1 in
    let phi = unmeta_monadic f in
    let uu____7480 = destruct_base_conn phi in
    FStar_Util.catch_opt uu____7480
      (fun uu____7485  ->
         let uu____7486 = destruct_q_conn phi in
         FStar_Util.catch_opt uu____7486
           (fun uu____7491  ->
              let uu____7492 = destruct_sq_base_conn phi in
              FStar_Util.catch_opt uu____7492
                (fun uu____7497  ->
                   let uu____7498 = destruct_sq_forall phi in
                   FStar_Util.catch_opt uu____7498
                     (fun uu____7503  ->
                        let uu____7504 = destruct_sq_exists phi in
                        FStar_Util.catch_opt uu____7504
                          (fun uu____7508  -> FStar_Pervasives_Native.None)))))
let action_as_lb:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____7518 =
          let uu____7523 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational
              FStar_Pervasives_Native.None in
          FStar_Util.Inr uu____7523 in
        let uu____7524 =
          let uu____7525 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
          arrow a.FStar_Syntax_Syntax.action_params uu____7525 in
        let uu____7528 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None in
        close_univs_and_mk_letbinding uu____7518
          a.FStar_Syntax_Syntax.action_univs uu____7524
          FStar_Parser_Const.effect_Tot_lid uu____7528 in
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
    let uu____7552 =
      let uu____7555 =
        let uu____7556 =
          let uu____7571 =
            let uu____7574 = FStar_Syntax_Syntax.as_arg t in [uu____7574] in
          (reify_, uu____7571) in
        FStar_Syntax_Syntax.Tm_app uu____7556 in
      FStar_Syntax_Syntax.mk uu____7555 in
    uu____7552 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
let rec delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____7587 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____7613 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____7614 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____7615 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____7638 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____7655 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____7656 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____7657 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7671) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____7676;
           FStar_Syntax_Syntax.index = uu____7677;
           FStar_Syntax_Syntax.sort = t2;_},uu____7679)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____7687) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7693,uu____7694) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____7736) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____7757,t2,uu____7759) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____7780,t2) -> delta_qualifier t2
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
  fun t  -> let uu____7808 = delta_qualifier t in incr_delta_depth uu____7808
let is_unknown: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____7813 =
      let uu____7814 = FStar_Syntax_Subst.compress t in
      uu____7814.FStar_Syntax_Syntax.n in
    match uu____7813 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____7817 -> false
let rec list_elements:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____7830 = let uu____7845 = unmeta e in head_and_args uu____7845 in
    match uu____7830 with
    | (head1,args) ->
        let uu____7872 =
          let uu____7885 =
            let uu____7886 = un_uinst head1 in
            uu____7886.FStar_Syntax_Syntax.n in
          (uu____7885, args) in
        (match uu____7872 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____7902) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____7922::(hd1,uu____7924)::(tl1,uu____7926)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____7973 =
               let uu____7978 =
                 let uu____7983 = list_elements tl1 in
                 FStar_Util.must uu____7983 in
               hd1 :: uu____7978 in
             FStar_Pervasives_Native.Some uu____7973
         | uu____7996 -> FStar_Pervasives_Native.None)
let rec apply_last:
  'Auu____8017 .
    ('Auu____8017 -> 'Auu____8017) ->
      'Auu____8017 Prims.list -> 'Auu____8017 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____8040 = f a in [uu____8040]
      | x::xs -> let uu____8045 = apply_last f xs in x :: uu____8045
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
          let uu____8086 =
            let uu____8089 =
              let uu____8090 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
              FStar_Syntax_Syntax.Tm_fvar uu____8090 in
            FStar_Syntax_Syntax.mk uu____8089 in
          uu____8086 FStar_Pervasives_Native.None rng in
        let cons1 args pos =
          let uu____8103 =
            let uu____8104 =
              let uu____8105 = ctor FStar_Parser_Const.cons_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____8105
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____8104 args in
          uu____8103 FStar_Pervasives_Native.None pos in
        let nil args pos =
          let uu____8117 =
            let uu____8118 =
              let uu____8119 = ctor FStar_Parser_Const.nil_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____8119
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____8118 args in
          uu____8117 FStar_Pervasives_Native.None pos in
        let uu____8122 =
          let uu____8123 =
            let uu____8124 = FStar_Syntax_Syntax.iarg typ in [uu____8124] in
          nil uu____8123 rng in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____8130 =
                 let uu____8131 = FStar_Syntax_Syntax.iarg typ in
                 let uu____8132 =
                   let uu____8135 = FStar_Syntax_Syntax.as_arg t in
                   let uu____8136 =
                     let uu____8139 = FStar_Syntax_Syntax.as_arg a in
                     [uu____8139] in
                   uu____8135 :: uu____8136 in
                 uu____8131 :: uu____8132 in
               cons1 uu____8130 t.FStar_Syntax_Syntax.pos) l uu____8122
let uvar_from_id:
  Prims.int ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun id  ->
    fun t  ->
      let uu____8150 =
        let uu____8153 =
          let uu____8154 =
            let uu____8171 = FStar_Syntax_Unionfind.from_id id in
            (uu____8171, t) in
          FStar_Syntax_Syntax.Tm_uvar uu____8154 in
        FStar_Syntax_Syntax.mk uu____8153 in
      uu____8150 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
        | uu____8234 -> false
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
          | uu____8337 -> false
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
        | uu____8485 -> false
let rec term_eq:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool
  =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_app uu____8604 ->
            let uu____8619 = head_and_args' t in
            (match uu____8619 with
             | (hd1,args) ->
                 let uu___169_8652 = t in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.pos =
                     (uu___169_8652.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___169_8652.FStar_Syntax_Syntax.vars)
                 })
        | uu____8663 -> t in
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
      | (uu____8934,uu____8935) -> false
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
      | (uu____9032,uu____9033) -> false
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
  fun uu____9040  ->
    fun uu____9041  ->
      match (uu____9040, uu____9041) with | ((p1,w1,t1),(p2,w2,t2)) -> false
let rec bottom_fold:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f in
      let tn =
        let uu____9181 = FStar_Syntax_Subst.compress t in
        uu____9181.FStar_Syntax_Syntax.n in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____9207 =
              let uu____9222 = ff f1 in
              let uu____9223 =
                FStar_List.map
                  (fun uu____9242  ->
                     match uu____9242 with
                     | (a,q) -> let uu____9253 = ff a in (uu____9253, q))
                  args in
              (uu____9222, uu____9223) in
            FStar_Syntax_Syntax.Tm_app uu____9207
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____9283 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____9283 with
             | (bs1,t') ->
                 let t'' = ff t' in
                 let uu____9291 =
                   let uu____9308 = FStar_Syntax_Subst.close bs1 t'' in
                   (bs1, uu____9308, k) in
                 FStar_Syntax_Syntax.Tm_abs uu____9291)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____9335 = let uu____9342 = ff t1 in (uu____9342, us) in
            FStar_Syntax_Syntax.Tm_uinst uu____9335
        | uu____9343 -> tn in
      f
        (let uu___170_9346 = t in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.pos = (uu___170_9346.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___170_9346.FStar_Syntax_Syntax.vars)
         })
let rec sizeof: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____9351 ->
        let uu____9376 =
          let uu____9377 = FStar_Syntax_Subst.compress t in sizeof uu____9377 in
        (Prims.parse_int "1") + uu____9376
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____9379 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____9379
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____9381 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____9381
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____9388 = sizeof t1 in (FStar_List.length us) + uu____9388
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____9391) ->
        let uu____9412 = sizeof t1 in
        let uu____9413 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____9424  ->
                 match uu____9424 with
                 | (bv,uu____9430) ->
                     let uu____9431 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu____9431) (Prims.parse_int "0") bs in
        uu____9412 + uu____9413
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9454 = sizeof hd1 in
        let uu____9455 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____9466  ->
                 match uu____9466 with
                 | (arg,uu____9472) ->
                     let uu____9473 = sizeof arg in acc + uu____9473)
            (Prims.parse_int "0") args in
        uu____9454 + uu____9455
    | uu____9474 -> Prims.parse_int "1"
let is_synth_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____9479 =
      let uu____9480 = un_uinst t in uu____9480.FStar_Syntax_Syntax.n in
    match uu____9479 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
    | uu____9484 -> false
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
        let uu____9510 =
          let uu____9513 =
            let uu____9514 =
              let uu____9521 =
                let uu____9522 =
                  let uu____9527 = FStar_Dyn.mkdyn b in (uu____9527, s) in
                FStar_Syntax_Syntax.Meta_alien uu____9522 in
              (FStar_Syntax_Syntax.tun, uu____9521) in
            FStar_Syntax_Syntax.Tm_meta uu____9514 in
          FStar_Syntax_Syntax.mk uu____9513 in
        uu____9510 FStar_Pervasives_Native.None
          (match r with
           | FStar_Pervasives_Native.Some r1 -> r1
           | FStar_Pervasives_Native.None  -> FStar_Range.dummyRange)
let un_alien: FStar_Syntax_Syntax.term -> FStar_Dyn.dyn =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        (uu____9539,FStar_Syntax_Syntax.Meta_alien (blob,uu____9541)) -> blob
    | uu____9546 -> failwith "unexpected: term was not an alien embedding"