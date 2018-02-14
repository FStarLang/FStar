open Prims
let qual_id: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun id1  ->
      let uu____7 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1]) in
      FStar_Ident.set_lid_range uu____7 id1.FStar_Ident.idRange
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
  'Auu____17 .
    (FStar_Syntax_Syntax.bv,'Auu____17) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term,'Auu____17) FStar_Pervasives_Native.tuple2
  =
  fun uu____29  ->
    match uu____29 with
    | (b,imp) ->
        let uu____36 = FStar_Syntax_Syntax.bv_to_name b in (uu____36, imp)
let args_of_non_null_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____59 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____59
            then []
            else (let uu____71 = arg_of_non_null_binder b in [uu____71])))
let args_of_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2
  =
  fun binders  ->
    let uu____95 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____141 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____141
              then
                let b1 =
                  let uu____159 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  (uu____159, (FStar_Pervasives_Native.snd b)) in
                let uu____160 = arg_of_non_null_binder b1 in (b1, uu____160)
              else
                (let uu____174 = arg_of_non_null_binder b in (b, uu____174)))) in
    FStar_All.pipe_right uu____95 FStar_List.unzip
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
              let uu____256 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____256
              then
                let uu____261 = b in
                match uu____261 with
                | (a,imp) ->
                    let b1 =
                      let uu____269 =
                        let uu____270 = FStar_Util.string_of_int i in
                        Prims.strcat "_" uu____270 in
                      FStar_Ident.id_of_text uu____269 in
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
        let uu____302 =
          let uu____305 =
            let uu____306 =
              let uu____319 = name_binders binders in (uu____319, comp) in
            FStar_Syntax_Syntax.Tm_arrow uu____306 in
          FStar_Syntax_Syntax.mk uu____305 in
        uu____302 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____337 -> t
let null_binders_of_tks:
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____377  ->
            match uu____377 with
            | (t,imp) ->
                let uu____388 =
                  let uu____389 = FStar_Syntax_Syntax.null_binder t in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____389 in
                (uu____388, imp)))
let binders_of_tks:
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____439  ->
            match uu____439 with
            | (t,imp) ->
                let uu____456 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t in
                (uu____456, imp)))
let binders_of_freevars:
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list
  =
  fun fvs  ->
    let uu____466 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____466
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
let mk_subst: 'Auu____475 . 'Auu____475 -> 'Auu____475 Prims.list =
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
          (fun uu____562  ->
             fun uu____563  ->
               match (uu____562, uu____563) with
               | ((x,uu____581),(y,uu____583)) ->
                   let uu____592 =
                     let uu____599 = FStar_Syntax_Syntax.bv_to_name y in
                     (x, uu____599) in
                   FStar_Syntax_Syntax.NT uu____592) replace_xs with_ys
      else failwith "Ill-formed substitution"
let rec unmeta: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____606) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____612,uu____613) -> unmeta e2
    | uu____654 -> e1
let rec unmeta_safe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____665 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____672 -> e1
         | FStar_Syntax_Syntax.Meta_alien uu____681 -> e1
         | uu____690 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____692,uu____693) ->
        unmeta_safe e2
    | uu____734 -> e1
let rec univ_kernel:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____746 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____747 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____757 = univ_kernel u1 in
        (match uu____757 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____768 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____775 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let constant_univ_as_nat: FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  ->
    let uu____783 = univ_kernel u in FStar_Pervasives_Native.snd uu____783
let rec compare_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____794,uu____795) ->
          failwith "Impossible: compare_univs"
      | (uu____796,FStar_Syntax_Syntax.U_bvar uu____797) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_unknown ,uu____798) -> - (Prims.parse_int "1")
      | (uu____799,FStar_Syntax_Syntax.U_unknown ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_zero ,uu____800) -> - (Prims.parse_int "1")
      | (uu____801,FStar_Syntax_Syntax.U_zero ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____804,FStar_Syntax_Syntax.U_unif
         uu____805) -> - (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____814,FStar_Syntax_Syntax.U_name
         uu____815) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____842 = FStar_Syntax_Unionfind.univ_uvar_id u11 in
          let uu____843 = FStar_Syntax_Unionfind.univ_uvar_id u21 in
          uu____842 - uu____843
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1 in
          let n2 = FStar_List.length us2 in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____874 = FStar_List.zip us1 us2 in
               FStar_Util.find_map uu____874
                 (fun uu____889  ->
                    match uu____889 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21 in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None) in
             match copt with
             | FStar_Pervasives_Native.None  -> Prims.parse_int "0"
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____903,uu____904) ->
          - (Prims.parse_int "1")
      | (uu____907,FStar_Syntax_Syntax.U_max uu____908) ->
          Prims.parse_int "1"
      | uu____911 ->
          let uu____916 = univ_kernel u1 in
          (match uu____916 with
           | (k1,n1) ->
               let uu____923 = univ_kernel u2 in
               (match uu____923 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2 in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
let eq_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____938 = compare_univs u1 u2 in
      uu____938 = (Prims.parse_int "0")
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
    | FStar_Syntax_Syntax.Total uu____963 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____972 ->
        FStar_Parser_Const.effect_GTot_lid
let comp_flags:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____992 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1001 ->
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
            let uu____1038 =
              let uu____1039 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____1039 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____1038;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
        | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
            let uu____1066 =
              let uu____1067 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____1067 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____1066;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            } in
      let uu___73_1084 = c in
      let uu____1085 =
        let uu____1086 =
          let uu___74_1087 = comp_to_comp_typ c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___74_1087.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___74_1087.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___74_1087.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___74_1087.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu____1086 in
      {
        FStar_Syntax_Syntax.n = uu____1085;
        FStar_Syntax_Syntax.pos = (uu___73_1084.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___73_1084.FStar_Syntax_Syntax.vars)
      }
let lcomp_set_flags:
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1102 -> c
        | FStar_Syntax_Syntax.GTotal uu____1111 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___75_1122 = ct in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___75_1122.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___75_1122.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___75_1122.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___75_1122.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              } in
            let uu___76_1123 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___76_1123.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___76_1123.FStar_Syntax_Syntax.vars)
            } in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1126  ->
           let uu____1127 = FStar_Syntax_Syntax.lcomp_comp lc in
           comp_typ_set_flags uu____1127)
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
    | uu____1160 ->
        failwith "Assertion failed: Computation type without universe"
let is_named_tot:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1169 -> true
    | FStar_Syntax_Syntax.GTotal uu____1178 -> false
let is_total_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___61_1197  ->
               match uu___61_1197 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1198 -> false)))
let is_total_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___62_1205  ->
               match uu___62_1205 with
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
            (fun uu___63_1213  ->
               match uu___63_1213 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1214 -> false)))
let is_partial_return:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___64_1225  ->
            match uu___64_1225 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1226 -> false))
let is_lcomp_partial_return: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___65_1233  ->
            match uu___65_1233 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1234 -> false))
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
    | FStar_Syntax_Syntax.Total uu____1252 -> true
    | FStar_Syntax_Syntax.GTotal uu____1261 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___66_1274  ->
                   match uu___66_1274 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1275 -> false)))
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
            (fun uu___67_1292  ->
               match uu___67_1292 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1293 -> false)))
let is_pure_or_ghost_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
let is_pure_or_ghost_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1300 =
      let uu____1301 = FStar_Syntax_Subst.compress t in
      uu____1301.FStar_Syntax_Syntax.n in
    match uu____1300 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1304,c) -> is_pure_or_ghost_comp c
    | uu____1322 -> true
let is_lemma_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1331 -> false
let is_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1335 =
      let uu____1336 = FStar_Syntax_Subst.compress t in
      uu____1336.FStar_Syntax_Syntax.n in
    match uu____1335 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1339,c) -> is_lemma_comp c
    | uu____1357 -> false
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
    | uu____1422 -> (t1, [])
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
        let uu____1487 = head_and_args' head1 in
        (match uu____1487 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1544 -> (t1, [])
let un_uinst: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1564) ->
        FStar_Syntax_Subst.compress t2
    | uu____1569 -> t1
let is_smt_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1573 =
      let uu____1574 = FStar_Syntax_Subst.compress t in
      uu____1574.FStar_Syntax_Syntax.n in
    match uu____1573 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1577,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1599)::uu____1600 ->
                  let pats' = unmeta pats in
                  let uu____1644 = head_and_args pats' in
                  (match uu____1644 with
                   | (head1,uu____1660) ->
                       let uu____1681 =
                         let uu____1682 = un_uinst head1 in
                         uu____1682.FStar_Syntax_Syntax.n in
                       (match uu____1681 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1686 -> false))
              | uu____1687 -> false)
         | uu____1696 -> false)
    | uu____1697 -> false
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
                (fun uu___68_1709  ->
                   match uu___68_1709 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1710 -> false)))
    | uu____1711 -> false
let comp_result:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1724) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1734) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let set_result_typ:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____1754 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____1763 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___77_1775 = ct in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___77_1775.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___77_1775.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___77_1775.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___77_1775.FStar_Syntax_Syntax.flags)
             })
let is_trivial_wp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___69_1786  ->
            match uu___69_1786 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____1787 -> false))
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
    | uu____1803 -> false
let rec unascribe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1809,uu____1810) ->
        unascribe e2
    | uu____1851 -> e1
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1899,uu____1900) ->
          ascribe t' k
      | uu____1941 ->
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
    match projectee with | Equal  -> true | uu____1965 -> false
let uu___is_NotEqual: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1969 -> false
let uu___is_Unknown: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1973 -> false
let injectives: Prims.string Prims.list =
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
let rec eq_tm:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        let uu____1996 =
          let uu____2009 = unascribe t in head_and_args' uu____2009 in
        match uu____1996 with
        | (hd1,args) ->
            FStar_Syntax_Syntax.mk_Tm_app hd1 args
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
      let equal_if uu___70_2039 = if uu___70_2039 then Equal else Unknown in
      let equal_iff uu___71_2044 = if uu___71_2044 then Equal else NotEqual in
      let eq_and f g = match f with | Equal  -> g () | uu____2058 -> Unknown in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2066) -> NotEqual
        | (uu____2067,NotEqual ) -> NotEqual
        | (Unknown ,uu____2068) -> Unknown
        | (uu____2069,Unknown ) -> Unknown in
      let equal_data f1 args1 f2 args2 =
        let uu____2107 = FStar_Syntax_Syntax.fv_eq f1 f2 in
        if uu____2107
        then
          let uu____2111 = FStar_List.zip args1 args2 in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2169  ->
                    match uu____2169 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2197 = eq_tm a1 a2 in eq_inj acc uu____2197)
               Equal) uu____2111
        else NotEqual in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
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
            (let uu____2218 = FStar_Syntax_Syntax.fv_eq f g in
             equal_if uu____2218)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2231 = eq_tm f g in
          eq_and uu____2231
            (fun uu____2234  ->
               let uu____2235 = eq_univs_list us vs in equal_if uu____2235)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2236),uu____2237) -> Unknown
      | (uu____2238,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2239)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2242 = FStar_Const.eq_const c d in equal_iff uu____2242
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2244),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2246)) ->
          let uu____2295 = FStar_Syntax_Unionfind.equiv u1 u2 in
          equal_if uu____2295
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2340 =
            let uu____2345 =
              let uu____2346 = un_uinst h1 in
              uu____2346.FStar_Syntax_Syntax.n in
            let uu____2349 =
              let uu____2350 = un_uinst h2 in
              uu____2350.FStar_Syntax_Syntax.n in
            (uu____2345, uu____2349) in
          (match uu____2340 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (f1.FStar_Syntax_Syntax.fv_qual =
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
                 &&
                 (f2.FStar_Syntax_Syntax.fv_qual =
                    (FStar_Pervasives_Native.Some
                       FStar_Syntax_Syntax.Data_ctor))
               -> equal_data f1 args1 f2 args2
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____2362 =
                    let uu____2363 = FStar_Syntax_Syntax.lid_of_fv f1 in
                    FStar_Ident.string_of_lid uu____2363 in
                  FStar_List.mem uu____2362 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____2364 ->
               let uu____2369 = eq_tm h1 h2 in
               eq_and uu____2369 (fun uu____2371  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____2374 = eq_univs u v1 in equal_if uu____2374
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____2376),uu____2377) ->
          eq_tm t12 t21
      | (uu____2382,FStar_Syntax_Syntax.Tm_meta (t22,uu____2384)) ->
          eq_tm t11 t22
      | uu____2389 -> Unknown
and eq_args:
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____2425)::a11,(b,uu____2428)::b1) ->
          let uu____2482 = eq_tm a b in
          (match uu____2482 with
           | Equal  -> eq_args a11 b1
           | uu____2483 -> Unknown)
      | uu____2484 -> Unknown
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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____2496) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2502,uu____2503) ->
        unrefine t2
    | uu____2544 -> t1
let rec is_unit: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2548 =
      let uu____2549 = unrefine t in uu____2549.FStar_Syntax_Syntax.n in
    match uu____2548 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2554) -> is_unit t1
    | uu____2559 -> false
let rec non_informative: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2563 =
      let uu____2564 = unrefine t in uu____2564.FStar_Syntax_Syntax.n in
    match uu____2563 with
    | FStar_Syntax_Syntax.Tm_type uu____2567 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____2570) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2592) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____2597,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____2615 -> false
let is_fun: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____2619 =
      let uu____2620 = FStar_Syntax_Subst.compress e in
      uu____2620.FStar_Syntax_Syntax.n in
    match uu____2619 with
    | FStar_Syntax_Syntax.Tm_abs uu____2623 -> true
    | uu____2640 -> false
let is_function_typ: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2644 =
      let uu____2645 = FStar_Syntax_Subst.compress t in
      uu____2645.FStar_Syntax_Syntax.n in
    match uu____2644 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2648 -> true
    | uu____2661 -> false
let rec pre_typ: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____2667) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2673,uu____2674) ->
        pre_typ t2
    | uu____2715 -> t1
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
      let uu____2733 =
        let uu____2734 = un_uinst typ1 in uu____2734.FStar_Syntax_Syntax.n in
      match uu____2733 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1 in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____2789 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____2813 -> FStar_Pervasives_Native.None
let lids_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____2829,lids) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____2835,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2846,uu____2847,uu____2848,uu____2849,uu____2850) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____2860,uu____2861,uu____2862,uu____2863) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____2869,uu____2870,uu____2871,uu____2872,uu____2873) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2879,uu____2880) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2882,uu____2883) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____2886 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____2887 -> []
    | FStar_Syntax_Syntax.Sig_main uu____2888 -> []
let lid_of_sigelt:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____2899 -> FStar_Pervasives_Native.None
let quals_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals
let range_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng
let range_of_lb:
  'Auu____2913 'Auu____2914 .
    ((FStar_Syntax_Syntax.bv,FStar_Ident.lid) FStar_Util.either,'Auu____2914,
      'Auu____2913) FStar_Pervasives_Native.tuple3 -> FStar_Range.range
  =
  fun uu___72_2928  ->
    match uu___72_2928 with
    | (FStar_Util.Inl x,uu____2940,uu____2941) ->
        FStar_Syntax_Syntax.range_of_bv x
    | (FStar_Util.Inr l,uu____2947,uu____2948) -> FStar_Ident.range_of_lid l
let range_of_arg:
  'Auu____2956 'Auu____2957 .
    ('Auu____2957 FStar_Syntax_Syntax.syntax,'Auu____2956)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____2967  ->
    match uu____2967 with | (hd1,uu____2975) -> hd1.FStar_Syntax_Syntax.pos
let range_of_args:
  'Auu____2984 'Auu____2985 .
    ('Auu____2985 FStar_Syntax_Syntax.syntax,'Auu____2984)
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
          let uu____3105 =
            let uu____3108 =
              let uu____3109 =
                let uu____3116 =
                  FStar_Syntax_Syntax.fvar l
                    FStar_Syntax_Syntax.Delta_constant
                    (FStar_Pervasives_Native.Some
                       FStar_Syntax_Syntax.Data_ctor) in
                (uu____3116,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Data_app)) in
              FStar_Syntax_Syntax.Tm_meta uu____3109 in
            FStar_Syntax_Syntax.mk uu____3108 in
          uu____3105 FStar_Pervasives_Native.None
            (FStar_Ident.range_of_lid l)
      | uu____3120 ->
          let e =
            let uu____3132 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            mk_app uu____3132 args in
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
      let uu____3143 =
        let uu____3148 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9") in
        (uu____3148, (x.FStar_Ident.idRange)) in
      FStar_Ident.mk_ident uu____3143
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
          let uu____3183 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____3183
          then
            let uu____3184 =
              let uu____3189 =
                let uu____3190 = FStar_Util.string_of_int i in
                Prims.strcat "_" uu____3190 in
              let uu____3191 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____3189, uu____3191) in
            FStar_Ident.mk_ident uu____3184
          else x.FStar_Syntax_Syntax.ppname in
        let y =
          let uu___78_3194 = x in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___78_3194.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___78_3194.FStar_Syntax_Syntax.sort)
          } in
        let uu____3195 = mk_field_projector_name_from_ident lid nm in
        (uu____3195, y)
let set_uvar:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun uv  ->
    fun t  ->
      let uu____3202 = FStar_Syntax_Unionfind.find uv in
      match uu____3202 with
      | FStar_Pervasives_Native.Some uu____3205 ->
          let uu____3206 =
            let uu____3207 =
              let uu____3208 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu____3208 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3207 in
          failwith uu____3206
      | uu____3209 -> FStar_Syntax_Unionfind.change uv t
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
      | uu____3280 -> q1 = q2
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
              let uu____3311 =
                let uu___79_3312 = rc in
                let uu____3313 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs) in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___79_3312.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____3313;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___79_3312.FStar_Syntax_Syntax.residual_flags)
                } in
              FStar_Pervasives_Native.Some uu____3311 in
        match bs with
        | [] -> t
        | uu____3324 ->
            let body =
              let uu____3326 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____3326 in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____3354 =
                   let uu____3357 =
                     let uu____3358 =
                       let uu____3375 =
                         let uu____3382 = FStar_Syntax_Subst.close_binders bs in
                         FStar_List.append uu____3382 bs' in
                       let uu____3393 = close_lopt lopt' in
                       (uu____3375, t1, uu____3393) in
                     FStar_Syntax_Syntax.Tm_abs uu____3358 in
                   FStar_Syntax_Syntax.mk uu____3357 in
                 uu____3354 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____3409 ->
                 let uu____3416 =
                   let uu____3419 =
                     let uu____3420 =
                       let uu____3437 = FStar_Syntax_Subst.close_binders bs in
                       let uu____3438 = close_lopt lopt in
                       (uu____3437, body, uu____3438) in
                     FStar_Syntax_Syntax.Tm_abs uu____3420 in
                   FStar_Syntax_Syntax.mk uu____3419 in
                 uu____3416 FStar_Pervasives_Native.None
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
      | uu____3476 ->
          let uu____3483 =
            let uu____3486 =
              let uu____3487 =
                let uu____3500 = FStar_Syntax_Subst.close_binders bs in
                let uu____3501 = FStar_Syntax_Subst.close_comp bs c in
                (uu____3500, uu____3501) in
              FStar_Syntax_Syntax.Tm_arrow uu____3487 in
            FStar_Syntax_Syntax.mk uu____3486 in
          uu____3483 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
let flat_arrow:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c in
      let uu____3532 =
        let uu____3533 = FStar_Syntax_Subst.compress t in
        uu____3533.FStar_Syntax_Syntax.n in
      match uu____3532 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____3559) ->
               let uu____3568 =
                 let uu____3569 = FStar_Syntax_Subst.compress tres in
                 uu____3569.FStar_Syntax_Syntax.n in
               (match uu____3568 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____3604 -> t)
           | uu____3605 -> t)
      | uu____3606 -> t
let refine:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____3615 =
        let uu____3616 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____3616 t.FStar_Syntax_Syntax.pos in
      let uu____3617 =
        let uu____3620 =
          let uu____3621 =
            let uu____3628 =
              let uu____3629 =
                let uu____3630 = FStar_Syntax_Syntax.mk_binder b in
                [uu____3630] in
              FStar_Syntax_Subst.close uu____3629 t in
            (b, uu____3628) in
          FStar_Syntax_Syntax.Tm_refine uu____3621 in
        FStar_Syntax_Syntax.mk uu____3620 in
      uu____3617 FStar_Pervasives_Native.None uu____3615
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
        let uu____3679 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____3679 with
         | (bs1,c1) ->
             let uu____3696 = is_tot_or_gtot_comp c1 in
             if uu____3696
             then
               let uu____3707 = arrow_formals_comp (comp_result c1) in
               (match uu____3707 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____3753;
           FStar_Syntax_Syntax.index = uu____3754;
           FStar_Syntax_Syntax.sort = k2;_},uu____3756)
        -> arrow_formals_comp k2
    | uu____3763 ->
        let uu____3764 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3764)
let rec arrow_formals:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let uu____3790 = arrow_formals_comp k in
    match uu____3790 with | (bs,c) -> (bs, (comp_result c))
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
          let uu____3866 =
            let uu___80_3867 = rc in
            let uu____3868 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___80_3867.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____3868;
              FStar_Syntax_Syntax.residual_flags =
                (uu___80_3867.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____3866
      | uu____3875 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____3903 =
        let uu____3904 =
          let uu____3907 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____3907 in
        uu____3904.FStar_Syntax_Syntax.n in
      match uu____3903 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____3945 = aux t2 what in
          (match uu____3945 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____4005 -> ([], t1, abs_body_lcomp) in
    let uu____4018 = aux t FStar_Pervasives_Native.None in
    match uu____4018 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____4060 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____4060 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp in
             (bs1, t2, abs_body_lcomp1))
let mk_letbinding:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
              -> FStar_Syntax_Syntax.letbinding
  =
  fun lbname  ->
    fun univ_vars  ->
      fun typ  ->
        fun eff  ->
          fun def  ->
            fun lbattrs  ->
              {
                FStar_Syntax_Syntax.lbname = lbname;
                FStar_Syntax_Syntax.lbunivs = univ_vars;
                FStar_Syntax_Syntax.lbtyp = typ;
                FStar_Syntax_Syntax.lbeff = eff;
                FStar_Syntax_Syntax.lbdef = def;
                FStar_Syntax_Syntax.lbattrs = lbattrs
              }
let close_univs_and_mk_letbinding:
  FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Ident.ident Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
                -> FStar_Syntax_Syntax.letbinding
  =
  fun recs  ->
    fun lbname  ->
      fun univ_vars  ->
        fun typ  ->
          fun eff  ->
            fun def  ->
              fun attrs  ->
                let def1 =
                  match (recs, univ_vars) with
                  | (FStar_Pervasives_Native.None ,uu____4185) -> def
                  | (uu____4196,[]) -> def
                  | (FStar_Pervasives_Native.Some fvs,uu____4208) ->
                      let universes =
                        FStar_All.pipe_right univ_vars
                          (FStar_List.map
                             (fun _0_27  -> FStar_Syntax_Syntax.U_name _0_27)) in
                      let inst1 =
                        FStar_All.pipe_right fvs
                          (FStar_List.map
                             (fun fv  ->
                                (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                  universes))) in
                      FStar_Syntax_InstFV.instantiate inst1 def in
                let typ1 = FStar_Syntax_Subst.close_univ_vars univ_vars typ in
                let def2 = FStar_Syntax_Subst.close_univ_vars univ_vars def1 in
                mk_letbinding lbname univ_vars typ1 eff def2 attrs
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
            let uu____4308 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____4308 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____4337 ->
            let t' = arrow binders c in
            let uu____4347 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____4347 with
             | (uvs1,t'1) ->
                 let uu____4366 =
                   let uu____4367 = FStar_Syntax_Subst.compress t'1 in
                   uu____4367.FStar_Syntax_Syntax.n in
                 (match uu____4366 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____4408 -> failwith "Impossible"))
let is_tuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____4425 -> false
let is_dtuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____4430 -> false
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
      let uu____4462 =
        let uu____4463 = pre_typ t in uu____4463.FStar_Syntax_Syntax.n in
      match uu____4462 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____4467 -> false
let rec is_constructed_typ:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____4474 =
        let uu____4475 = pre_typ t in uu____4475.FStar_Syntax_Syntax.n in
      match uu____4474 with
      | FStar_Syntax_Syntax.Tm_fvar uu____4478 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____4480) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4502) ->
          is_constructed_typ t1 lid
      | uu____4507 -> false
let rec get_tycon:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____4516 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____4517 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____4518 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____4520) -> get_tycon t2
    | uu____4541 -> FStar_Pervasives_Native.None
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
    let uu____4551 =
      let uu____4552 = un_uinst t in uu____4552.FStar_Syntax_Syntax.n in
    match uu____4551 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Parser_Const.fstar_refl_embed_lid
    | uu____4556 -> false
let is_fstar_tactics_quote: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4560 =
      let uu____4561 = un_uinst t in uu____4561.FStar_Syntax_Syntax.n in
    match uu____4560 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.quote_lid
    | uu____4565 -> false
let is_fstar_tactics_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4569 =
      let uu____4570 = un_uinst t in uu____4570.FStar_Syntax_Syntax.n in
    match uu____4569 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____4574 -> false
let is_builtin_tactic: FStar_Ident.lident -> Prims.bool =
  fun md  ->
    let path = FStar_Ident.path_of_lid md in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____4581 =
        let uu____4584 = FStar_List.splitAt (Prims.parse_int "2") path in
        FStar_Pervasives_Native.fst uu____4584 in
      match uu____4581 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____4597 -> false
    else false
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
  fun uu____4611  ->
    let u =
      let uu____4617 = FStar_Syntax_Unionfind.univ_fresh () in
      FStar_All.pipe_left (fun _0_28  -> FStar_Syntax_Syntax.U_unif _0_28)
        uu____4617 in
    let uu____4634 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange in
    (uu____4634, u)
let attr_substitute: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  let uu____4641 =
    let uu____4644 =
      let uu____4645 =
        let uu____4646 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange in
        FStar_Syntax_Syntax.lid_as_fv uu____4646
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
      FStar_Syntax_Syntax.Tm_fvar uu____4645 in
    FStar_Syntax_Syntax.mk uu____4644 in
  uu____4641 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
let exp_char: FStar_BaseTypes.char -> FStar_Syntax_Syntax.term =
  fun c  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c))
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
let tac_opaque_attr: FStar_Syntax_Syntax.term = exp_string "tac_opaque"
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
          let uu____4693 =
            let uu____4696 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            let uu____4697 =
              let uu____4700 =
                let uu____4701 =
                  let uu____4716 =
                    let uu____4719 = FStar_Syntax_Syntax.as_arg phi11 in
                    let uu____4720 =
                      let uu____4723 = FStar_Syntax_Syntax.as_arg phi2 in
                      [uu____4723] in
                    uu____4719 :: uu____4720 in
                  (tand, uu____4716) in
                FStar_Syntax_Syntax.Tm_app uu____4701 in
              FStar_Syntax_Syntax.mk uu____4700 in
            uu____4697 FStar_Pervasives_Native.None uu____4696 in
          FStar_Pervasives_Native.Some uu____4693
let mk_binop:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____4746 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos in
        let uu____4747 =
          let uu____4750 =
            let uu____4751 =
              let uu____4766 =
                let uu____4769 = FStar_Syntax_Syntax.as_arg phi1 in
                let uu____4770 =
                  let uu____4773 = FStar_Syntax_Syntax.as_arg phi2 in
                  [uu____4773] in
                uu____4769 :: uu____4770 in
              (op_t, uu____4766) in
            FStar_Syntax_Syntax.Tm_app uu____4751 in
          FStar_Syntax_Syntax.mk uu____4750 in
        uu____4747 FStar_Pervasives_Native.None uu____4746
let mk_neg:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun phi  ->
    let uu____4786 =
      let uu____4789 =
        let uu____4790 =
          let uu____4805 =
            let uu____4808 = FStar_Syntax_Syntax.as_arg phi in [uu____4808] in
          (t_not, uu____4805) in
        FStar_Syntax_Syntax.Tm_app uu____4790 in
      FStar_Syntax_Syntax.mk uu____4789 in
    uu____4786 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
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
    let uu____4869 =
      let uu____4872 =
        let uu____4873 =
          let uu____4888 =
            let uu____4891 = FStar_Syntax_Syntax.as_arg e in [uu____4891] in
          (b2t_v, uu____4888) in
        FStar_Syntax_Syntax.Tm_app uu____4873 in
      FStar_Syntax_Syntax.mk uu____4872 in
    uu____4869 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
let teq: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.eq2_lid
let mk_untyped_eq2:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun e1  ->
    fun e2  ->
      let uu____4905 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos in
      let uu____4906 =
        let uu____4909 =
          let uu____4910 =
            let uu____4925 =
              let uu____4928 = FStar_Syntax_Syntax.as_arg e1 in
              let uu____4929 =
                let uu____4932 = FStar_Syntax_Syntax.as_arg e2 in
                [uu____4932] in
              uu____4928 :: uu____4929 in
            (teq, uu____4925) in
          FStar_Syntax_Syntax.Tm_app uu____4910 in
        FStar_Syntax_Syntax.mk uu____4909 in
      uu____4906 FStar_Pervasives_Native.None uu____4905
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
          let uu____4951 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          let uu____4952 =
            let uu____4955 =
              let uu____4956 =
                let uu____4971 =
                  let uu____4974 = FStar_Syntax_Syntax.iarg t in
                  let uu____4975 =
                    let uu____4978 = FStar_Syntax_Syntax.as_arg e1 in
                    let uu____4979 =
                      let uu____4982 = FStar_Syntax_Syntax.as_arg e2 in
                      [uu____4982] in
                    uu____4978 :: uu____4979 in
                  uu____4974 :: uu____4975 in
                (eq_inst, uu____4971) in
              FStar_Syntax_Syntax.Tm_app uu____4956 in
            FStar_Syntax_Syntax.mk uu____4955 in
          uu____4952 FStar_Pervasives_Native.None uu____4951
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
        let uu____5005 =
          let uu____5008 =
            let uu____5009 =
              let uu____5024 =
                let uu____5027 = FStar_Syntax_Syntax.iarg t in
                let uu____5028 =
                  let uu____5031 = FStar_Syntax_Syntax.as_arg x in
                  let uu____5032 =
                    let uu____5035 = FStar_Syntax_Syntax.as_arg t' in
                    [uu____5035] in
                  uu____5031 :: uu____5032 in
                uu____5027 :: uu____5028 in
              (t_has_type1, uu____5024) in
            FStar_Syntax_Syntax.Tm_app uu____5009 in
          FStar_Syntax_Syntax.mk uu____5008 in
        uu____5005 FStar_Pervasives_Native.None FStar_Range.dummyRange
let mk_with_type:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun u  ->
    fun t  ->
      fun e  ->
        let t_with_type =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        let t_with_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst (t_with_type, [u]))
            FStar_Pervasives_Native.None FStar_Range.dummyRange in
        let uu____5060 =
          let uu____5063 =
            let uu____5064 =
              let uu____5079 =
                let uu____5082 = FStar_Syntax_Syntax.iarg t in
                let uu____5083 =
                  let uu____5086 = FStar_Syntax_Syntax.as_arg e in
                  [uu____5086] in
                uu____5082 :: uu____5083 in
              (t_with_type1, uu____5079) in
            FStar_Syntax_Syntax.Tm_app uu____5064 in
          FStar_Syntax_Syntax.mk uu____5063 in
        uu____5060 FStar_Pervasives_Native.None FStar_Range.dummyRange
let lex_t: FStar_Syntax_Syntax.term = fvar_const FStar_Parser_Const.lex_t_lid
let lex_top: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  let uu____5096 =
    let uu____5099 =
      let uu____5100 =
        let uu____5107 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
        (uu____5107, [FStar_Syntax_Syntax.U_zero]) in
      FStar_Syntax_Syntax.Tm_uinst uu____5100 in
    FStar_Syntax_Syntax.mk uu____5099 in
  uu____5096 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
    let uu____5120 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____5133 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____5144 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags)) in
    match uu____5120 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____5165  -> c0)
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
        let uu____5221 =
          let uu____5224 =
            let uu____5225 =
              let uu____5240 =
                let uu____5243 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
                let uu____5244 =
                  let uu____5247 =
                    let uu____5248 =
                      let uu____5249 =
                        let uu____5250 = FStar_Syntax_Syntax.mk_binder x in
                        [uu____5250] in
                      abs uu____5249 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0)) in
                    FStar_Syntax_Syntax.as_arg uu____5248 in
                  [uu____5247] in
                uu____5243 :: uu____5244 in
              (fa, uu____5240) in
            FStar_Syntax_Syntax.Tm_app uu____5225 in
          FStar_Syntax_Syntax.mk uu____5224 in
        uu____5221 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
             let uu____5289 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____5289
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
let rec is_wild_pat:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____5298 -> true
    | uu____5299 -> false
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
          let uu____5338 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos in
          (uu____5338, FStar_Pervasives_Native.None, t1) in
        let else_branch =
          let uu____5366 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos in
          (uu____5366, FStar_Pervasives_Native.None, t2) in
        let uu____5379 =
          let uu____5380 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____5380 in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____5379
let mk_squash:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
          FStar_Pervasives_Native.None in
      let uu____5450 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u] in
      let uu____5453 =
        let uu____5462 = FStar_Syntax_Syntax.as_arg p in [uu____5462] in
      mk_app uu____5450 uu____5453
let mk_auto_squash:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
          FStar_Pervasives_Native.None in
      let uu____5472 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u] in
      let uu____5475 =
        let uu____5484 = FStar_Syntax_Syntax.as_arg p in [uu____5484] in
      mk_app uu____5472 uu____5475
let un_squash:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____5492 = head_and_args t in
    match uu____5492 with
    | (head1,args) ->
        let uu____5533 =
          let uu____5546 =
            let uu____5547 = un_uinst head1 in
            uu____5547.FStar_Syntax_Syntax.n in
          (uu____5546, args) in
        (match uu____5533 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____5564)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____5616 =
                    let uu____5621 =
                      let uu____5622 = FStar_Syntax_Syntax.mk_binder b in
                      [uu____5622] in
                    FStar_Syntax_Subst.open_term uu____5621 p in
                  (match uu____5616 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____5651 -> failwith "impossible" in
                       let uu____5656 =
                         let uu____5657 = FStar_Syntax_Free.names p1 in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____5657 in
                       if uu____5656
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____5667 -> FStar_Pervasives_Native.None)
         | uu____5670 -> FStar_Pervasives_Native.None)
let is_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____5696 = head_and_args t in
    match uu____5696 with
    | (head1,args) ->
        let uu____5741 =
          let uu____5754 =
            let uu____5755 = FStar_Syntax_Subst.compress head1 in
            uu____5755.FStar_Syntax_Syntax.n in
          (uu____5754, args) in
        (match uu____5741 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____5775;
               FStar_Syntax_Syntax.vars = uu____5776;_},u::[]),(t1,uu____5779)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____5818 -> FStar_Pervasives_Native.None)
let is_auto_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____5848 = head_and_args t in
    match uu____5848 with
    | (head1,args) ->
        let uu____5893 =
          let uu____5906 =
            let uu____5907 = FStar_Syntax_Subst.compress head1 in
            uu____5907.FStar_Syntax_Syntax.n in
          (uu____5906, args) in
        (match uu____5893 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____5927;
               FStar_Syntax_Syntax.vars = uu____5928;_},u::[]),(t1,uu____5931)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____5970 -> FStar_Pervasives_Native.None)
let is_sub_singleton: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____5992 = let uu____6007 = unmeta t in head_and_args uu____6007 in
    match uu____5992 with
    | (head1,uu____6009) ->
        let uu____6030 =
          let uu____6031 = un_uinst head1 in uu____6031.FStar_Syntax_Syntax.n in
        (match uu____6030 with
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
         | uu____6035 -> false)
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____6051 =
      let uu____6064 =
        let uu____6065 = FStar_Syntax_Subst.compress t in
        uu____6065.FStar_Syntax_Syntax.n in
      match uu____6064 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____6174 =
            let uu____6183 =
              let uu____6184 = arrow bs c in
              FStar_Syntax_Syntax.mk_Total uu____6184 in
            (b, uu____6183) in
          FStar_Pervasives_Native.Some uu____6174
      | uu____6197 -> FStar_Pervasives_Native.None in
    FStar_Util.bind_opt uu____6051
      (fun uu____6233  ->
         match uu____6233 with
         | (b,c) ->
             let uu____6268 = FStar_Syntax_Subst.open_comp [b] c in
             (match uu____6268 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____6315 ->
                        failwith
                          "impossible: open_comp returned different amount of binders" in
                  FStar_Pervasives_Native.Some (b1, c1)))
let is_free_in:
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun bv  ->
    fun t  ->
      let uu____6338 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____6338
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
    match projectee with | QAll _0 -> true | uu____6381 -> false
let __proj__QAll__item___0:
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QAll _0 -> _0
let uu___is_QEx: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____6417 -> false
let __proj__QEx__item___0:
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QEx _0 -> _0
let uu___is_BaseConn: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____6451 -> false
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____6484) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____6496) ->
          unmeta_monadic t
      | uu____6509 -> f2 in
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
      let aux f2 uu____6587 =
        match uu____6587 with
        | (lid,arity) ->
            let uu____6596 =
              let uu____6611 = unmeta_monadic f2 in head_and_args uu____6611 in
            (match uu____6596 with
             | (t,args) ->
                 let t1 = un_uinst t in
                 let uu____6637 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity) in
                 if uu____6637
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None) in
      FStar_Util.find_map connectives (aux f1) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____6712 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____6712)
      | uu____6723 -> ([], t1) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu____6770 = head_and_args t1 in
        match uu____6770 with
        | (t2,args) ->
            let uu____6817 = un_uinst t2 in
            let uu____6818 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6851  ->
                      match uu____6851 with
                      | (t3,imp) ->
                          let uu____6862 = unascribe t3 in (uu____6862, imp))) in
            (uu____6817, uu____6818) in
      let rec aux qopt out t1 =
        let uu____6897 = let uu____6914 = flat t1 in (qopt, uu____6914) in
        match uu____6897 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____6941;
                 FStar_Syntax_Syntax.vars = uu____6942;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____6945);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____6946;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____6947;_},uu____6948)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____7025;
                 FStar_Syntax_Syntax.vars = uu____7026;_},uu____7027::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____7030);
                  FStar_Syntax_Syntax.pos = uu____7031;
                  FStar_Syntax_Syntax.vars = uu____7032;_},uu____7033)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7121;
               FStar_Syntax_Syntax.vars = uu____7122;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____7125);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7126;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7127;_},uu____7128)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7204;
               FStar_Syntax_Syntax.vars = uu____7205;_},uu____7206::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____7209);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____7210;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____7211;_},uu____7212)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____7300) ->
            let bs = FStar_List.rev out in
            let uu____7334 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____7334 with
             | (bs1,t2) ->
                 let uu____7343 = patterns t2 in
                 (match uu____7343 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____7405 -> FStar_Pervasives_Native.None in
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
      let uu____7471 = un_squash t in
      FStar_Util.bind_opt uu____7471
        (fun t1  ->
           let uu____7487 = head_and_args' t1 in
           match uu____7487 with
           | (hd1,args) ->
               let uu____7520 =
                 let uu____7525 =
                   let uu____7526 = un_uinst hd1 in
                   uu____7526.FStar_Syntax_Syntax.n in
                 (uu____7525, (FStar_List.length args)) in
               (match uu____7520 with
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
                | uu____7609 -> FStar_Pervasives_Native.None)) in
    let rec destruct_sq_forall t =
      let uu____7632 = un_squash t in
      FStar_Util.bind_opt uu____7632
        (fun t1  ->
           let uu____7647 = arrow_one t1 in
           match uu____7647 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____7662 =
                 let uu____7663 = is_tot_or_gtot_comp c in
                 Prims.op_Negation uu____7663 in
               if uu____7662
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____7670 = comp_to_comp_typ c in
                    uu____7670.FStar_Syntax_Syntax.result_typ in
                  let uu____7671 =
                    is_free_in (FStar_Pervasives_Native.fst b) q in
                  if uu____7671
                  then
                    let uu____7674 = patterns q in
                    match uu____7674 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____7730 =
                       let uu____7731 =
                         let uu____7736 =
                           let uu____7739 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let uu____7740 =
                             let uu____7743 = FStar_Syntax_Syntax.as_arg q in
                             [uu____7743] in
                           uu____7739 :: uu____7740 in
                         (FStar_Parser_Const.imp_lid, uu____7736) in
                       BaseConn uu____7731 in
                     FStar_Pervasives_Native.Some uu____7730))
           | uu____7746 -> FStar_Pervasives_Native.None)
    and destruct_sq_exists t =
      let uu____7754 = un_squash t in
      FStar_Util.bind_opt uu____7754
        (fun t1  ->
           let uu____7785 = head_and_args' t1 in
           match uu____7785 with
           | (hd1,args) ->
               let uu____7818 =
                 let uu____7831 =
                   let uu____7832 = un_uinst hd1 in
                   uu____7832.FStar_Syntax_Syntax.n in
                 (uu____7831, args) in
               (match uu____7818 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____7847)::(a2,uu____7849)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____7884 =
                      let uu____7885 = FStar_Syntax_Subst.compress a2 in
                      uu____7885.FStar_Syntax_Syntax.n in
                    (match uu____7884 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____7892) ->
                         let uu____7919 = FStar_Syntax_Subst.open_term [b] q in
                         (match uu____7919 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____7958 -> failwith "impossible" in
                              let uu____7963 = patterns q1 in
                              (match uu____7963 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____8030 -> FStar_Pervasives_Native.None)
                | uu____8031 -> FStar_Pervasives_Native.None))
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____8052 = destruct_sq_forall phi in
          (match uu____8052 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8074 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____8080 = destruct_sq_exists phi in
          (match uu____8080 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8102 -> f1)
      | uu____8105 -> f1 in
    let phi = unmeta_monadic f in
    let uu____8109 = destruct_base_conn phi in
    FStar_Util.catch_opt uu____8109
      (fun uu____8114  ->
         let uu____8115 = destruct_q_conn phi in
         FStar_Util.catch_opt uu____8115
           (fun uu____8120  ->
              let uu____8121 = destruct_sq_base_conn phi in
              FStar_Util.catch_opt uu____8121
                (fun uu____8126  ->
                   let uu____8127 = destruct_sq_forall phi in
                   FStar_Util.catch_opt uu____8127
                     (fun uu____8132  ->
                        let uu____8133 = destruct_sq_exists phi in
                        FStar_Util.catch_opt uu____8133
                          (fun uu____8137  -> FStar_Pervasives_Native.None)))))
let unthunk_lemma_post:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let uu____8143 =
      let uu____8144 = FStar_Syntax_Subst.compress t in
      uu____8144.FStar_Syntax_Syntax.n in
    match uu____8143 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____8151) ->
        let uu____8178 = FStar_Syntax_Subst.open_term [b] e in
        (match uu____8178 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs in
             let uu____8204 = is_free_in (FStar_Pervasives_Native.fst b1) e1 in
             if uu____8204
             then
               let uu____8207 =
                 let uu____8216 = FStar_Syntax_Syntax.as_arg exp_unit in
                 [uu____8216] in
               mk_app t uu____8207
             else e1)
    | uu____8218 ->
        let uu____8219 =
          let uu____8228 = FStar_Syntax_Syntax.as_arg exp_unit in
          [uu____8228] in
        mk_app t uu____8219
let action_as_lb:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____8236 =
          let uu____8241 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational
              FStar_Pervasives_Native.None in
          FStar_Util.Inr uu____8241 in
        let uu____8242 =
          let uu____8243 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
          arrow a.FStar_Syntax_Syntax.action_params uu____8243 in
        let uu____8246 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None in
        close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____8236
          a.FStar_Syntax_Syntax.action_univs uu____8242
          FStar_Parser_Const.effect_Tot_lid uu____8246 [] in
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
    let uu____8273 =
      let uu____8276 =
        let uu____8277 =
          let uu____8292 =
            let uu____8295 = FStar_Syntax_Syntax.as_arg t in [uu____8295] in
          (reify_, uu____8292) in
        FStar_Syntax_Syntax.Tm_app uu____8277 in
      FStar_Syntax_Syntax.mk uu____8276 in
    uu____8273 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
let rec delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____8307 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____8333 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____8334 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____8335 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____8358 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____8375 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____8376 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____8377 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____8391) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____8396;
           FStar_Syntax_Syntax.index = uu____8397;
           FStar_Syntax_Syntax.sort = t2;_},uu____8399)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____8407) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____8413,uu____8414) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8456) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____8477,t2,uu____8479) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____8500,t2) -> delta_qualifier t2
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
  fun t  -> let uu____8526 = delta_qualifier t in incr_delta_depth uu____8526
let is_unknown: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____8530 =
      let uu____8531 = FStar_Syntax_Subst.compress t in
      uu____8531.FStar_Syntax_Syntax.n in
    match uu____8530 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____8534 -> false
let rec list_elements:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____8546 = let uu____8561 = unmeta e in head_and_args uu____8561 in
    match uu____8546 with
    | (head1,args) ->
        let uu____8588 =
          let uu____8601 =
            let uu____8602 = un_uinst head1 in
            uu____8602.FStar_Syntax_Syntax.n in
          (uu____8601, args) in
        (match uu____8588 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____8618) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____8638::(hd1,uu____8640)::(tl1,uu____8642)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____8689 =
               let uu____8694 =
                 let uu____8699 = list_elements tl1 in
                 FStar_Util.must uu____8699 in
               hd1 :: uu____8694 in
             FStar_Pervasives_Native.Some uu____8689
         | uu____8712 -> FStar_Pervasives_Native.None)
let rec apply_last:
  'Auu____8730 .
    ('Auu____8730 -> 'Auu____8730) ->
      'Auu____8730 Prims.list -> 'Auu____8730 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____8753 = f a in [uu____8753]
      | x::xs -> let uu____8758 = apply_last f xs in x :: uu____8758
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
          let uu____8794 =
            let uu____8797 =
              let uu____8798 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
              FStar_Syntax_Syntax.Tm_fvar uu____8798 in
            FStar_Syntax_Syntax.mk uu____8797 in
          uu____8794 FStar_Pervasives_Native.None rng in
        let cons1 args pos =
          let uu____8811 =
            let uu____8812 =
              let uu____8813 = ctor FStar_Parser_Const.cons_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____8813
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____8812 args in
          uu____8811 FStar_Pervasives_Native.None pos in
        let nil args pos =
          let uu____8825 =
            let uu____8826 =
              let uu____8827 = ctor FStar_Parser_Const.nil_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____8827
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____8826 args in
          uu____8825 FStar_Pervasives_Native.None pos in
        let uu____8830 =
          let uu____8831 =
            let uu____8832 = FStar_Syntax_Syntax.iarg typ in [uu____8832] in
          nil uu____8831 rng in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____8838 =
                 let uu____8839 = FStar_Syntax_Syntax.iarg typ in
                 let uu____8840 =
                   let uu____8843 = FStar_Syntax_Syntax.as_arg t in
                   let uu____8844 =
                     let uu____8847 = FStar_Syntax_Syntax.as_arg a in
                     [uu____8847] in
                   uu____8843 :: uu____8844 in
                 uu____8839 :: uu____8840 in
               cons1 uu____8838 t.FStar_Syntax_Syntax.pos) l uu____8830
let uvar_from_id:
  Prims.int ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun id1  ->
    fun t  ->
      let uu____8856 =
        let uu____8859 =
          let uu____8860 =
            let uu____8877 = FStar_Syntax_Unionfind.from_id id1 in
            (uu____8877, t) in
          FStar_Syntax_Syntax.Tm_uvar uu____8860 in
        FStar_Syntax_Syntax.mk uu____8859 in
      uu____8856 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
        | uu____8937 -> false
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
          | uu____9034 -> false
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
        | uu____9172 -> false
let rec term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_app uu____9283 ->
            let uu____9298 = head_and_args' t in
            (match uu____9298 with
             | (hd1,args) ->
                 let uu___81_9331 = t in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.pos =
                     (uu___81_9331.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___81_9331.FStar_Syntax_Syntax.vars)
                 })
        | uu____9342 -> t in
      let t11 = let uu____9346 = unmeta_safe t1 in canon_app uu____9346 in
      let t21 = let uu____9352 = unmeta_safe t2 in canon_app uu____9352 in
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
      | (uu____9619,uu____9620) -> false
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
      | (uu____9715,uu____9716) -> false
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
  fun uu____9723  ->
    fun uu____9724  ->
      match (uu____9723, uu____9724) with | ((p1,w1,t1),(p2,w2,t2)) -> false
let rec bottom_fold:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f in
      let tn =
        let uu____9862 = FStar_Syntax_Subst.compress t in
        uu____9862.FStar_Syntax_Syntax.n in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____9888 =
              let uu____9903 = ff f1 in
              let uu____9904 =
                FStar_List.map
                  (fun uu____9923  ->
                     match uu____9923 with
                     | (a,q) -> let uu____9934 = ff a in (uu____9934, q))
                  args in
              (uu____9903, uu____9904) in
            FStar_Syntax_Syntax.Tm_app uu____9888
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____9964 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____9964 with
             | (bs1,t') ->
                 let t'' = ff t' in
                 let uu____9972 =
                   let uu____9989 = FStar_Syntax_Subst.close bs1 t'' in
                   (bs1, uu____9989, k) in
                 FStar_Syntax_Syntax.Tm_abs uu____9972)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____10016 = let uu____10023 = ff t1 in (uu____10023, us) in
            FStar_Syntax_Syntax.Tm_uinst uu____10016
        | uu____10024 -> tn in
      f
        (let uu___82_10027 = t in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.pos = (uu___82_10027.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___82_10027.FStar_Syntax_Syntax.vars)
         })
let rec sizeof: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10031 ->
        let uu____10056 =
          let uu____10057 = FStar_Syntax_Subst.compress t in
          sizeof uu____10057 in
        (Prims.parse_int "1") + uu____10056
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____10059 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____10059
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____10061 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____10061
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____10068 = sizeof t1 in (FStar_List.length us) + uu____10068
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____10071) ->
        let uu____10092 = sizeof t1 in
        let uu____10093 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____10104  ->
                 match uu____10104 with
                 | (bv,uu____10110) ->
                     let uu____10111 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu____10111) (Prims.parse_int "0") bs in
        uu____10092 + uu____10093
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____10134 = sizeof hd1 in
        let uu____10135 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____10146  ->
                 match uu____10146 with
                 | (arg,uu____10152) ->
                     let uu____10153 = sizeof arg in acc + uu____10153)
            (Prims.parse_int "0") args in
        uu____10134 + uu____10135
    | uu____10154 -> Prims.parse_int "1"
let is_fvar: FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun lid  ->
    fun t  ->
      let uu____10161 =
        let uu____10162 = un_uinst t in uu____10162.FStar_Syntax_Syntax.n in
      match uu____10161 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____10166 -> false
let is_synth_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  -> is_fvar FStar_Parser_Const.synth_lid t
let mk_alien:
  'a .
    FStar_Syntax_Syntax.typ ->
      'a ->
        Prims.string ->
          FStar_Range.range FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.term
  =
  fun ty  ->
    fun b  ->
      fun s  ->
        fun r  ->
          let uu____10196 =
            let uu____10199 =
              let uu____10200 =
                let uu____10207 =
                  let uu____10208 =
                    let uu____10217 = FStar_Dyn.mkdyn b in
                    (uu____10217, s, ty) in
                  FStar_Syntax_Syntax.Meta_alien uu____10208 in
                (FStar_Syntax_Syntax.tun, uu____10207) in
              FStar_Syntax_Syntax.Tm_meta uu____10200 in
            FStar_Syntax_Syntax.mk uu____10199 in
          uu____10196 FStar_Pervasives_Native.None
            (match r with
             | FStar_Pervasives_Native.Some r1 -> r1
             | FStar_Pervasives_Native.None  -> FStar_Range.dummyRange)
let un_alien: FStar_Syntax_Syntax.term -> FStar_Dyn.dyn =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        (uu____10227,FStar_Syntax_Syntax.Meta_alien
         (blob,uu____10229,uu____10230))
        -> blob
    | uu____10239 -> failwith "unexpected: term was not an alien embedding"
let process_pragma:
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> Prims.unit =
  fun p  ->
    fun r  ->
      let set_options1 t s =
        let uu____10253 = FStar_Options.set_options t s in
        match uu____10253 with
        | FStar_Getopt.Success  -> ()
        | FStar_Getopt.Help  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                "Failed to process pragma: use 'fstar --help' to see which options are available")
              r
        | FStar_Getopt.Error s1 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                (Prims.strcat "Failed to process pragma: " s1)) r in
      match p with
      | FStar_Syntax_Syntax.LightOff  ->
          if p = FStar_Syntax_Syntax.LightOff
          then FStar_Options.set_ml_ish ()
          else ()
      | FStar_Syntax_Syntax.SetOptions o -> set_options1 FStar_Options.Set o
      | FStar_Syntax_Syntax.ResetOptions sopt ->
          ((let uu____10261 = FStar_Options.restore_cmd_line_options false in
            FStar_All.pipe_right uu____10261 FStar_Pervasives.ignore);
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))