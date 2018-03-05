open Prims
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____7 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____7 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    FStar_Ident.lid_of_ids
      (FStar_List.append lid.FStar_Ident.ns
         [FStar_Ident.mk_ident
            ((Prims.strcat FStar_Ident.reserved_prefix
                (Prims.strcat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))])
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____17 .
    (FStar_Syntax_Syntax.bv,'Auu____17) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term,'Auu____17) FStar_Pervasives_Native.tuple2
  =
  fun uu____29  ->
    match uu____29 with
    | (b,imp) ->
        let uu____36 = FStar_Syntax_Syntax.bv_to_name b  in (uu____36, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____59 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____59
            then []
            else (let uu____71 = arg_of_non_null_binder b  in [uu____71])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  =
  fun binders  ->
    let uu____95 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____141 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____141
              then
                let b1 =
                  let uu____159 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____159, (FStar_Pervasives_Native.snd b))  in
                let uu____160 = arg_of_non_null_binder b1  in (b1, uu____160)
              else
                (let uu____174 = arg_of_non_null_binder b  in (b, uu____174))))
       in
    FStar_All.pipe_right uu____95 FStar_List.unzip
  
let (name_binders :
  FStar_Syntax_Syntax.binder Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____256 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____256
              then
                let uu____261 = b  in
                match uu____261 with
                | (a,imp) ->
                    let b1 =
                      let uu____269 =
                        let uu____270 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____270  in
                      FStar_Ident.id_of_text uu____269  in
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
        let uu____302 =
          let uu____305 =
            let uu____306 =
              let uu____319 = name_binders binders  in (uu____319, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____306  in
          FStar_Syntax_Syntax.mk uu____305  in
        uu____302 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____337 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____377  ->
            match uu____377 with
            | (t,imp) ->
                let uu____388 =
                  let uu____389 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____389
                   in
                (uu____388, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
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
                    t
                   in
                (uu____456, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____466 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____466
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____475 . 'Auu____475 -> 'Auu____475 Prims.list =
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
          (fun uu____562  ->
             fun uu____563  ->
               match (uu____562, uu____563) with
               | ((x,uu____581),(y,uu____583)) ->
                   let uu____592 =
                     let uu____599 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____599)  in
                   FStar_Syntax_Syntax.NT uu____592) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        (uu____605,FStar_Syntax_Syntax.Meta_quoted uu____606) -> e1
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____618) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____624,uu____625) -> unmeta e2
    | uu____666 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____677 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____684 -> e1
         | FStar_Syntax_Syntax.Meta_quoted uu____693 -> e1
         | uu____700 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____702,uu____703) ->
        unmeta_safe e2
    | uu____744 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____756 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____757 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____767 = univ_kernel u1  in
        (match uu____767 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____778 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____785 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____793 = univ_kernel u  in FStar_Pervasives_Native.snd uu____793
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____804,uu____805) ->
          failwith "Impossible: compare_univs"
      | (uu____806,FStar_Syntax_Syntax.U_bvar uu____807) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____808) ->
          ~- (Prims.parse_int "1")
      | (uu____809,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____810) -> ~- (Prims.parse_int "1")
      | (uu____811,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____814,FStar_Syntax_Syntax.U_unif
         uu____815) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____824,FStar_Syntax_Syntax.U_name
         uu____825) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____852 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____853 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____852 - uu____853
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____884 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____884
                 (fun uu____899  ->
                    match uu____899 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____913,uu____914) ->
          ~- (Prims.parse_int "1")
      | (uu____917,FStar_Syntax_Syntax.U_max uu____918) ->
          (Prims.parse_int "1")
      | uu____921 ->
          let uu____926 = univ_kernel u1  in
          (match uu____926 with
           | (k1,n1) ->
               let uu____933 = univ_kernel u2  in
               (match uu____933 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____948 = compare_univs u1 u2  in
      uu____948 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
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
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____973 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____982 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1002 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1011 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    fun f  ->
      let comp_to_comp_typ c1 =
        match c1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Comp c2 -> c2
        | FStar_Syntax_Syntax.Total (t,u_opt) ->
            let uu____1048 =
              let uu____1049 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
              FStar_Util.dflt [] uu____1049  in
            {
              FStar_Syntax_Syntax.comp_univs = uu____1048;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
        | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
            let uu____1076 =
              let uu____1077 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
              FStar_Util.dflt [] uu____1077  in
            {
              FStar_Syntax_Syntax.comp_univs = uu____1076;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
         in
      let uu___50_1094 = c  in
      let uu____1095 =
        let uu____1096 =
          let uu___51_1097 = comp_to_comp_typ c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___51_1097.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___51_1097.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___51_1097.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___51_1097.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1096  in
      {
        FStar_Syntax_Syntax.n = uu____1095;
        FStar_Syntax_Syntax.pos = (uu___50_1094.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___50_1094.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1112 -> c
        | FStar_Syntax_Syntax.GTotal uu____1121 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___52_1132 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___52_1132.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___52_1132.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___52_1132.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___52_1132.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___53_1133 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___53_1133.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___53_1133.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1136  ->
           let uu____1137 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1137)
  
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
    | uu____1170 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1179 -> true
    | FStar_Syntax_Syntax.GTotal uu____1188 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___38_1207  ->
               match uu___38_1207 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1208 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___39_1215  ->
               match uu___39_1215 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1216 -> false)))
  
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
            (fun uu___40_1223  ->
               match uu___40_1223 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1224 -> false)))
  
let (is_tac_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
      FStar_Parser_Const.effect_Tac_lid
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___41_1238  ->
            match uu___41_1238 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1239 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___42_1246  ->
            match uu___42_1246 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1247 -> false))
  
let (is_tot_or_gtot_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (is_total_comp c) ||
      (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid
         (comp_effect_name c))
  
let (is_tac_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_Ident.lid_equals FStar_Parser_Const.effect_Tac_lid
      (comp_effect_name c)
  
let (is_pure_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)
  
let (is_pure_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1272 -> true
    | FStar_Syntax_Syntax.GTotal uu____1281 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___43_1294  ->
                   match uu___43_1294 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1295 -> false)))
  
let (is_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)
  
let (is_pure_or_ghost_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  -> (is_pure_comp c) || (is_ghost_effect (comp_effect_name c)) 
let (is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___44_1312  ->
               match uu___44_1312 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1313 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1320 =
      let uu____1321 = FStar_Syntax_Subst.compress t  in
      uu____1321.FStar_Syntax_Syntax.n  in
    match uu____1320 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1324,c) -> is_pure_or_ghost_comp c
    | uu____1342 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1351 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1355 =
      let uu____1356 = FStar_Syntax_Subst.compress t  in
      uu____1356.FStar_Syntax_Syntax.n  in
    match uu____1355 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1359,c) -> is_lemma_comp c
    | uu____1377 -> false
  
let (head_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax,
                                                            FStar_Syntax_Syntax.aqual)
                                                            FStar_Pervasives_Native.tuple2
                                                            Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____1442 -> (t1, [])
  
let rec (head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.term'
                                 FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1507 = head_and_args' head1  in
        (match uu____1507 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1564 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1584) ->
        FStar_Syntax_Subst.compress t2
    | uu____1589 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1593 =
      let uu____1594 = FStar_Syntax_Subst.compress t  in
      uu____1594.FStar_Syntax_Syntax.n  in
    match uu____1593 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1597,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1619)::uu____1620 ->
                  let pats' = unmeta pats  in
                  let uu____1664 = head_and_args pats'  in
                  (match uu____1664 with
                   | (head1,uu____1680) ->
                       let uu____1701 =
                         let uu____1702 = un_uinst head1  in
                         uu____1702.FStar_Syntax_Syntax.n  in
                       (match uu____1701 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1706 -> false))
              | uu____1707 -> false)
         | uu____1716 -> false)
    | uu____1717 -> false
  
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
                (fun uu___45_1729  ->
                   match uu___45_1729 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1730 -> false)))
    | uu____1731 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1744) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1754) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____1774 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____1783 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___54_1795 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___54_1795.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___54_1795.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___54_1795.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___54_1795.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___46_1806  ->
            match uu___46_1806 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____1807 -> false))
  
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
    | uu____1823 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1829,uu____1830) ->
        unascribe e2
    | uu____1871 -> e1
  
let rec (ascribe :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.comp'
                                                             FStar_Syntax_Syntax.syntax)
       FStar_Util.either,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun k  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1919,uu____1920) ->
          ascribe t' k
      | uu____1961 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____1985 =
      let uu____1990 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____1990  in
    uu____1985 i.FStar_Syntax_Syntax.kind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2035 =
      let uu____2036 = FStar_Syntax_Subst.compress t  in
      uu____2036.FStar_Syntax_Syntax.n  in
    match uu____2035 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2040 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2040
    | uu____2041 -> t
  
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
            let uu____2071 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2071;
              FStar_Syntax_Syntax.kind = k;
              FStar_Syntax_Syntax.typ = typ;
              FStar_Syntax_Syntax.rng = rng
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i)
            FStar_Pervasives_Native.None rng
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown [@@deriving show]
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2075 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2079 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2083 -> false
  
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
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        let uu____2106 =
          let uu____2119 = unascribe t  in head_and_args' uu____2119  in
        match uu____2106 with
        | (hd1,args) ->
            FStar_Syntax_Syntax.mk_Tm_app hd1 args
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___47_2149 = if uu___47_2149 then Equal else Unknown  in
      let equal_iff uu___48_2154 = if uu___48_2154 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2168 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2176) -> NotEqual
        | (uu____2177,NotEqual ) -> NotEqual
        | (Unknown ,uu____2178) -> Unknown
        | (uu____2179,Unknown ) -> Unknown  in
      let notq t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (uu____2188,FStar_Syntax_Syntax.Meta_quoted uu____2189) -> false
        | uu____2200 -> true  in
      let equal_data f1 args1 f2 args2 =
        let uu____2238 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2238
        then
          let uu____2242 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2300  ->
                    match uu____2300 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2328 = eq_tm a1 a2  in
                        eq_inj acc uu____2328) Equal) uu____2242
        else NotEqual  in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2332,uu____2333) ->
          let uu____2334 = unlazy t11  in eq_tm uu____2334 t21
      | (uu____2335,FStar_Syntax_Syntax.Tm_lazy uu____2336) ->
          let uu____2337 = unlazy t21  in eq_tm t11 uu____2337
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
            (let uu____2355 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2355)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2368 = eq_tm f g  in
          eq_and uu____2368
            (fun uu____2371  ->
               let uu____2372 = eq_univs_list us vs  in equal_if uu____2372)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2373),uu____2374) -> Unknown
      | (uu____2375,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2376)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2379 = FStar_Const.eq_const c d  in equal_iff uu____2379
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2381),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2383)) ->
          let uu____2432 = FStar_Syntax_Unionfind.equiv u1 u2  in
          equal_if uu____2432
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2477 =
            let uu____2482 =
              let uu____2483 = un_uinst h1  in
              uu____2483.FStar_Syntax_Syntax.n  in
            let uu____2486 =
              let uu____2487 = un_uinst h2  in
              uu____2487.FStar_Syntax_Syntax.n  in
            (uu____2482, uu____2486)  in
          (match uu____2477 with
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
                 (let uu____2499 =
                    let uu____2500 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____2500  in
                  FStar_List.mem uu____2499 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____2501 ->
               let uu____2506 = eq_tm h1 h2  in
               eq_and uu____2506 (fun uu____2508  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____2511 = eq_univs u v1  in equal_if uu____2511
      | (FStar_Syntax_Syntax.Tm_meta (t1',uu____2513),uu____2514) when
          notq t11 -> eq_tm t1' t21
      | (uu____2519,FStar_Syntax_Syntax.Tm_meta (t2',uu____2521)) when
          notq t21 -> eq_tm t11 t2'
      | (FStar_Syntax_Syntax.Tm_meta
         (uu____2526,FStar_Syntax_Syntax.Meta_quoted (t12,uu____2528)),FStar_Syntax_Syntax.Tm_meta
         (uu____2529,FStar_Syntax_Syntax.Meta_quoted (t22,uu____2531))) ->
          eq_tm t12 t22
      | uu____2548 -> Unknown

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____2584)::a11,(b,uu____2587)::b1) ->
          let uu____2641 = eq_tm a b  in
          (match uu____2641 with
           | Equal  -> eq_args a11 b1
           | uu____2642 -> Unknown)
      | uu____2643 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____2655) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2661,uu____2662) ->
        unrefine t2
    | uu____2703 -> t1
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2707 =
      let uu____2708 = unrefine t  in uu____2708.FStar_Syntax_Syntax.n  in
    match uu____2707 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2713) -> is_unit t1
    | uu____2718 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2722 =
      let uu____2723 = unrefine t  in uu____2723.FStar_Syntax_Syntax.n  in
    match uu____2722 with
    | FStar_Syntax_Syntax.Tm_type uu____2726 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____2729) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2751) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____2756,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____2774 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____2778 =
      let uu____2779 = FStar_Syntax_Subst.compress e  in
      uu____2779.FStar_Syntax_Syntax.n  in
    match uu____2778 with
    | FStar_Syntax_Syntax.Tm_abs uu____2782 -> true
    | uu____2799 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2803 =
      let uu____2804 = FStar_Syntax_Subst.compress t  in
      uu____2804.FStar_Syntax_Syntax.n  in
    match uu____2803 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2807 -> true
    | uu____2820 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____2826) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2832,uu____2833) ->
        pre_typ t2
    | uu____2874 -> t1
  
let (destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ  in
      let uu____2892 =
        let uu____2893 = un_uinst typ1  in uu____2893.FStar_Syntax_Syntax.n
         in
      match uu____2892 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____2948 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____2972 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____2988,lids) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____2994,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3005,uu____3006,uu____3007,uu____3008,uu____3009) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____3019,uu____3020,uu____3021,uu____3022) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____3028,uu____3029,uu____3030,uu____3031,uu____3032) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3038,uu____3039) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3041,uu____3042) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3045 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____3046 -> []
    | FStar_Syntax_Syntax.Sig_main uu____3047 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____3058 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___49_3075  ->
    match uu___49_3075 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____3085 'Auu____3086 .
    ('Auu____3085 FStar_Syntax_Syntax.syntax,'Auu____3086)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____3096  ->
    match uu____3096 with | (hd1,uu____3104) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____3113 'Auu____3114 .
    ('Auu____3113 FStar_Syntax_Syntax.syntax,'Auu____3114)
      FStar_Pervasives_Native.tuple2 Prims.list ->
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
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun args  ->
      let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args))
        FStar_Pervasives_Native.None r
  
let (mk_data :
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun l  ->
    fun args  ->
      match args with
      | [] ->
          let uu____3234 =
            let uu____3237 =
              let uu____3238 =
                let uu____3245 =
                  FStar_Syntax_Syntax.fvar l
                    FStar_Syntax_Syntax.Delta_constant
                    (FStar_Pervasives_Native.Some
                       FStar_Syntax_Syntax.Data_ctor)
                   in
                (uu____3245,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Data_app))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____3238  in
            FStar_Syntax_Syntax.mk uu____3237  in
          uu____3234 FStar_Pervasives_Native.None
            (FStar_Ident.range_of_lid l)
      | uu____3249 ->
          let e =
            let uu____3261 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____3261 args  in
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_meta
               (e,
                 (FStar_Syntax_Syntax.Meta_desugared
                    FStar_Syntax_Syntax.Data_app)))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (mangle_field_name : FStar_Ident.ident -> FStar_Ident.ident) =
  fun x  ->
    FStar_Ident.mk_ident
      ((Prims.strcat "__fname__" x.FStar_Ident.idText),
        (x.FStar_Ident.idRange))
  
let (unmangle_field_name : FStar_Ident.ident -> FStar_Ident.ident) =
  fun x  ->
    if FStar_Util.starts_with x.FStar_Ident.idText "__fname__"
    then
      let uu____3272 =
        let uu____3277 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____3277, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____3272
    else x
  
let (field_projector_prefix : Prims.string) = "__proj__" 
let (field_projector_sep : Prims.string) = "__item__" 
let (field_projector_contains_constructor : Prims.string -> Prims.bool) =
  fun s  -> FStar_Util.starts_with s field_projector_prefix 
let (mk_field_projector_name_from_string :
  Prims.string -> Prims.string -> Prims.string) =
  fun constr  ->
    fun field  ->
      Prims.strcat field_projector_prefix
        (Prims.strcat constr (Prims.strcat field_projector_sep field))
  
let (mk_field_projector_name_from_ident :
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun lid  ->
    fun i  ->
      let j = unmangle_field_name i  in
      let jtext = j.FStar_Ident.idText  in
      let newi =
        if field_projector_contains_constructor jtext
        then j
        else
          FStar_Ident.mk_ident
            ((mk_field_projector_name_from_string
                (lid.FStar_Ident.ident).FStar_Ident.idText jtext),
              (i.FStar_Ident.idRange))
         in
      FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns [newi])
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv ->
      Prims.int ->
        (FStar_Ident.lident,FStar_Syntax_Syntax.bv)
          FStar_Pervasives_Native.tuple2)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____3312 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____3312
          then
            let uu____3313 =
              let uu____3318 =
                let uu____3319 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____3319  in
              let uu____3320 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____3318, uu____3320)  in
            FStar_Ident.mk_ident uu____3313
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___55_3323 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___55_3323.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___55_3323.FStar_Syntax_Syntax.sort)
          }  in
        let uu____3324 = mk_field_projector_name_from_ident lid nm  in
        (uu____3324, y)
  
let (set_uvar :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit) =
  fun uv  ->
    fun t  ->
      let uu____3331 = FStar_Syntax_Unionfind.find uv  in
      match uu____3331 with
      | FStar_Pervasives_Native.Some uu____3334 ->
          let uu____3335 =
            let uu____3336 =
              let uu____3337 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____3337  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3336  in
          failwith uu____3335
      | uu____3338 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____3409 -> q1 = q2
  
let (abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        let close_lopt lopt1 =
          match lopt1 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rc ->
              let uu____3440 =
                let uu___56_3441 = rc  in
                let uu____3442 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___56_3441.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____3442;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___56_3441.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____3440
           in
        match bs with
        | [] -> t
        | uu____3453 ->
            let body =
              let uu____3455 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____3455  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____3483 =
                   let uu____3486 =
                     let uu____3487 =
                       let uu____3504 =
                         let uu____3511 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____3511 bs'  in
                       let uu____3522 = close_lopt lopt'  in
                       (uu____3504, t1, uu____3522)  in
                     FStar_Syntax_Syntax.Tm_abs uu____3487  in
                   FStar_Syntax_Syntax.mk uu____3486  in
                 uu____3483 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____3538 ->
                 let uu____3545 =
                   let uu____3548 =
                     let uu____3549 =
                       let uu____3566 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____3567 = close_lopt lopt  in
                       (uu____3566, body, uu____3567)  in
                     FStar_Syntax_Syntax.Tm_abs uu____3549  in
                   FStar_Syntax_Syntax.mk uu____3548  in
                 uu____3545 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos)
  
let (arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____3605 ->
          let uu____3612 =
            let uu____3615 =
              let uu____3616 =
                let uu____3629 = FStar_Syntax_Subst.close_binders bs  in
                let uu____3630 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____3629, uu____3630)  in
              FStar_Syntax_Syntax.Tm_arrow uu____3616  in
            FStar_Syntax_Syntax.mk uu____3615  in
          uu____3612 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____3661 =
        let uu____3662 = FStar_Syntax_Subst.compress t  in
        uu____3662.FStar_Syntax_Syntax.n  in
      match uu____3661 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____3688) ->
               let uu____3697 =
                 let uu____3698 = FStar_Syntax_Subst.compress tres  in
                 uu____3698.FStar_Syntax_Syntax.n  in
               (match uu____3697 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____3733 -> t)
           | uu____3734 -> t)
      | uu____3735 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____3744 =
        let uu____3745 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____3745 t.FStar_Syntax_Syntax.pos  in
      let uu____3746 =
        let uu____3749 =
          let uu____3750 =
            let uu____3757 =
              let uu____3758 =
                let uu____3759 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____3759]  in
              FStar_Syntax_Subst.close uu____3758 t  in
            (b, uu____3757)  in
          FStar_Syntax_Syntax.Tm_refine uu____3750  in
        FStar_Syntax_Syntax.mk uu____3749  in
      uu____3746 FStar_Pervasives_Native.None uu____3744
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____3808 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____3808 with
         | (bs1,c1) ->
             let uu____3825 = is_tot_or_gtot_comp c1  in
             if uu____3825
             then
               let uu____3836 = arrow_formals_comp (comp_result c1)  in
               (match uu____3836 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____3882;
           FStar_Syntax_Syntax.index = uu____3883;
           FStar_Syntax_Syntax.sort = k2;_},uu____3885)
        -> arrow_formals_comp k2
    | uu____3892 ->
        let uu____3893 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____3893)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____3919 = arrow_formals_comp k  in
    match uu____3919 with | (bs,c) -> (bs, (comp_result c))
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.residual_comp
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3)
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____3995 =
            let uu___57_3996 = rc  in
            let uu____3997 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___57_3996.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____3997;
              FStar_Syntax_Syntax.residual_flags =
                (uu___57_3996.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____3995
      | uu____4004 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____4032 =
        let uu____4033 =
          let uu____4036 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____4036  in
        uu____4033.FStar_Syntax_Syntax.n  in
      match uu____4032 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____4074 = aux t2 what  in
          (match uu____4074 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____4134 -> ([], t1, abs_body_lcomp)  in
    let uu____4147 = aux t FStar_Pervasives_Native.None  in
    match uu____4147 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____4189 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____4189 with
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
              -> FStar_Syntax_Syntax.letbinding)
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
  
let (close_univs_and_mk_letbinding :
  FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Ident.ident Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
                -> FStar_Syntax_Syntax.letbinding)
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
                  | (FStar_Pervasives_Native.None ,uu____4314) -> def
                  | (uu____4325,[]) -> def
                  | (FStar_Pervasives_Native.Some fvs,uu____4337) ->
                      let universes =
                        FStar_All.pipe_right univ_vars
                          (FStar_List.map
                             (fun _0_27  -> FStar_Syntax_Syntax.U_name _0_27))
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
                let def2 = FStar_Syntax_Subst.close_univ_vars univ_vars def1
                   in
                mk_letbinding lbname univ_vars typ1 eff def2 attrs
  
let (open_univ_vars_binders_and_comp :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                          FStar_Pervasives_Native.tuple2
                                          Prims.list,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple3)
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____4437 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____4437 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____4466 ->
            let t' = arrow binders c  in
            let uu____4476 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____4476 with
             | (uvs1,t'1) ->
                 let uu____4495 =
                   let uu____4496 = FStar_Syntax_Subst.compress t'1  in
                   uu____4496.FStar_Syntax_Syntax.n  in
                 (match uu____4495 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____4537 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____4554 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____4559 -> false
  
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
      let uu____4591 =
        let uu____4592 = pre_typ t  in uu____4592.FStar_Syntax_Syntax.n  in
      match uu____4591 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____4596 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____4603 =
        let uu____4604 = pre_typ t  in uu____4604.FStar_Syntax_Syntax.n  in
      match uu____4603 with
      | FStar_Syntax_Syntax.Tm_fvar uu____4607 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____4609) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4631) ->
          is_constructed_typ t1 lid
      | uu____4636 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____4645 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____4646 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____4647 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____4649) -> get_tycon t2
    | uu____4670 -> FStar_Pervasives_Native.None
  
let (is_interpreted : FStar_Ident.lident -> Prims.bool) =
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
      FStar_Parser_Const.op_Negation]  in
    FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms
  
let (is_fstar_tactics_embed : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4680 =
      let uu____4681 = un_uinst t  in uu____4681.FStar_Syntax_Syntax.n  in
    match uu____4680 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Parser_Const.fstar_refl_embed_lid
    | uu____4685 -> false
  
let (is_fstar_tactics_quote : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4689 =
      let uu____4690 = un_uinst t  in uu____4690.FStar_Syntax_Syntax.n  in
    match uu____4689 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.quote_lid
    | uu____4694 -> false
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4698 =
      let uu____4699 = un_uinst t  in uu____4699.FStar_Syntax_Syntax.n  in
    match uu____4698 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____4703 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____4710 =
        let uu____4713 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____4713  in
      match uu____4710 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____4726 -> false
    else false
  
let (ktype : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (ktype0 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (type_u :
  Prims.unit ->
    (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____4740  ->
    let u =
      let uu____4746 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_28  -> FStar_Syntax_Syntax.U_unif _0_28)
        uu____4746
       in
    let uu____4763 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____4763, u)
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____4770 =
    let uu____4773 =
      let uu____4774 =
        let uu____4775 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____4775
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____4774  in
    FStar_Syntax_Syntax.mk uu____4773  in
  uu____4770 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (exp_true_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_false_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_unit : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
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
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
      FStar_Pervasives_Native.None
  
let (tand : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.and_lid 
let (tor : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.or_lid 
let (timp : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (tiff : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    FStar_Pervasives_Native.None
  
let (t_bool : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.bool_lid 
let (t_false : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.false_lid 
let (t_true : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.true_lid 
let (b2t_v : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.b2t_lid 
let (t_not : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.not_lid 
let (tac_opaque_attr : FStar_Syntax_Syntax.term) = exp_string "tac_opaque" 
let (mk_conj_opt :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu____4822 =
            let uu____4825 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____4826 =
              let uu____4829 =
                let uu____4830 =
                  let uu____4845 =
                    let uu____4848 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____4849 =
                      let uu____4852 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____4852]  in
                    uu____4848 :: uu____4849  in
                  (tand, uu____4845)  in
                FStar_Syntax_Syntax.Tm_app uu____4830  in
              FStar_Syntax_Syntax.mk uu____4829  in
            uu____4826 FStar_Pervasives_Native.None uu____4825  in
          FStar_Pervasives_Native.Some uu____4822
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____4875 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____4876 =
          let uu____4879 =
            let uu____4880 =
              let uu____4895 =
                let uu____4898 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____4899 =
                  let uu____4902 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____4902]  in
                uu____4898 :: uu____4899  in
              (op_t, uu____4895)  in
            FStar_Syntax_Syntax.Tm_app uu____4880  in
          FStar_Syntax_Syntax.mk uu____4879  in
        uu____4876 FStar_Pervasives_Native.None uu____4875
  
let (mk_neg :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____4915 =
      let uu____4918 =
        let uu____4919 =
          let uu____4934 =
            let uu____4937 = FStar_Syntax_Syntax.as_arg phi  in [uu____4937]
             in
          (t_not, uu____4934)  in
        FStar_Syntax_Syntax.Tm_app uu____4919  in
      FStar_Syntax_Syntax.mk uu____4918  in
    uu____4915 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
let (mk_conj :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tand phi1 phi2 
let (mk_conj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term) =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
  
let (mk_disj :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tor phi1 phi2 
let (mk_disj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term) =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
  
let (mk_imp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop timp phi1 phi2 
let (mk_iff :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop tiff phi1 phi2 
let (b2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e  ->
    let uu____4998 =
      let uu____5001 =
        let uu____5002 =
          let uu____5017 =
            let uu____5020 = FStar_Syntax_Syntax.as_arg e  in [uu____5020]
             in
          (b2t_v, uu____5017)  in
        FStar_Syntax_Syntax.Tm_app uu____5002  in
      FStar_Syntax_Syntax.mk uu____5001  in
    uu____4998 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____5034 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____5035 =
        let uu____5038 =
          let uu____5039 =
            let uu____5054 =
              let uu____5057 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____5058 =
                let uu____5061 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____5061]  in
              uu____5057 :: uu____5058  in
            (teq, uu____5054)  in
          FStar_Syntax_Syntax.Tm_app uu____5039  in
        FStar_Syntax_Syntax.mk uu____5038  in
      uu____5035 FStar_Pervasives_Native.None uu____5034
  
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
          let uu____5080 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____5081 =
            let uu____5084 =
              let uu____5085 =
                let uu____5100 =
                  let uu____5103 = FStar_Syntax_Syntax.iarg t  in
                  let uu____5104 =
                    let uu____5107 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____5108 =
                      let uu____5111 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____5111]  in
                    uu____5107 :: uu____5108  in
                  uu____5103 :: uu____5104  in
                (eq_inst, uu____5100)  in
              FStar_Syntax_Syntax.Tm_app uu____5085  in
            FStar_Syntax_Syntax.mk uu____5084  in
          uu____5081 FStar_Pervasives_Native.None uu____5080
  
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
        let uu____5134 =
          let uu____5137 =
            let uu____5138 =
              let uu____5153 =
                let uu____5156 = FStar_Syntax_Syntax.iarg t  in
                let uu____5157 =
                  let uu____5160 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____5161 =
                    let uu____5164 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____5164]  in
                  uu____5160 :: uu____5161  in
                uu____5156 :: uu____5157  in
              (t_has_type1, uu____5153)  in
            FStar_Syntax_Syntax.Tm_app uu____5138  in
          FStar_Syntax_Syntax.mk uu____5137  in
        uu____5134 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        let t_with_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst (t_with_type, [u]))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        let uu____5189 =
          let uu____5192 =
            let uu____5193 =
              let uu____5208 =
                let uu____5211 = FStar_Syntax_Syntax.iarg t  in
                let uu____5212 =
                  let uu____5215 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____5215]  in
                uu____5211 :: uu____5212  in
              (t_with_type1, uu____5208)  in
            FStar_Syntax_Syntax.Tm_app uu____5193  in
          FStar_Syntax_Syntax.mk uu____5192  in
        uu____5189 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu____5225 =
    let uu____5228 =
      let uu____5229 =
        let uu____5236 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____5236, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____5229  in
    FStar_Syntax_Syntax.mk uu____5228  in
  uu____5225 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (lex_pair : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (tforall : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (t_haseq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
  
let (lcomp_of_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.lcomp)
  =
  fun c0  ->
    let uu____5249 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____5262 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____5273 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____5249 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____5294  -> c0)
  
let (mk_residual_comp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.cflags Prims.list ->
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
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fa  ->
    fun x  ->
      fun body  ->
        let uu____5350 =
          let uu____5353 =
            let uu____5354 =
              let uu____5369 =
                let uu____5372 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____5373 =
                  let uu____5376 =
                    let uu____5377 =
                      let uu____5378 =
                        let uu____5379 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____5379]  in
                      abs uu____5378 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____5377  in
                  [uu____5376]  in
                uu____5372 :: uu____5373  in
              (fa, uu____5369)  in
            FStar_Syntax_Syntax.Tm_app uu____5354  in
          FStar_Syntax_Syntax.mk uu____5353  in
        uu____5350 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____5418 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____5418
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____5427 -> true
    | uu____5428 -> false
  
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
          let uu____5467 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____5467, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____5495 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____5495, FStar_Pervasives_Native.None, t2)  in
        let uu____5508 =
          let uu____5509 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____5509  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____5508
  
let (mk_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
          FStar_Pervasives_Native.None
         in
      let uu____5579 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____5582 =
        let uu____5591 = FStar_Syntax_Syntax.as_arg p  in [uu____5591]  in
      mk_app uu____5579 uu____5582
  
let (mk_auto_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
          FStar_Pervasives_Native.None
         in
      let uu____5601 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____5604 =
        let uu____5613 = FStar_Syntax_Syntax.as_arg p  in [uu____5613]  in
      mk_app uu____5601 uu____5604
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____5621 = head_and_args t  in
    match uu____5621 with
    | (head1,args) ->
        let uu____5662 =
          let uu____5675 =
            let uu____5676 = un_uinst head1  in
            uu____5676.FStar_Syntax_Syntax.n  in
          (uu____5675, args)  in
        (match uu____5662 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____5693)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____5745 =
                    let uu____5750 =
                      let uu____5751 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____5751]  in
                    FStar_Syntax_Subst.open_term uu____5750 p  in
                  (match uu____5745 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____5780 -> failwith "impossible"  in
                       let uu____5785 =
                         let uu____5786 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____5786
                          in
                       if uu____5785
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____5796 -> FStar_Pervasives_Native.None)
         | uu____5799 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____5825 = head_and_args t  in
    match uu____5825 with
    | (head1,args) ->
        let uu____5870 =
          let uu____5883 =
            let uu____5884 = FStar_Syntax_Subst.compress head1  in
            uu____5884.FStar_Syntax_Syntax.n  in
          (uu____5883, args)  in
        (match uu____5870 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____5904;
               FStar_Syntax_Syntax.vars = uu____5905;_},u::[]),(t1,uu____5908)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____5947 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____5977 = head_and_args t  in
    match uu____5977 with
    | (head1,args) ->
        let uu____6022 =
          let uu____6035 =
            let uu____6036 = FStar_Syntax_Subst.compress head1  in
            uu____6036.FStar_Syntax_Syntax.n  in
          (uu____6035, args)  in
        (match uu____6022 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____6056;
               FStar_Syntax_Syntax.vars = uu____6057;_},u::[]),(t1,uu____6060)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____6099 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____6121 = let uu____6136 = unmeta t  in head_and_args uu____6136
       in
    match uu____6121 with
    | (head1,uu____6138) ->
        let uu____6159 =
          let uu____6160 = un_uinst head1  in
          uu____6160.FStar_Syntax_Syntax.n  in
        (match uu____6159 with
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
         | uu____6164 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6180 =
      let uu____6193 =
        let uu____6194 = FStar_Syntax_Subst.compress t  in
        uu____6194.FStar_Syntax_Syntax.n  in
      match uu____6193 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____6303 =
            let uu____6312 =
              let uu____6313 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____6313  in
            (b, uu____6312)  in
          FStar_Pervasives_Native.Some uu____6303
      | uu____6326 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____6180
      (fun uu____6362  ->
         match uu____6362 with
         | (b,c) ->
             let uu____6397 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____6397 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____6444 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____6467 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6467
  
type qpats = FStar_Syntax_Syntax.args Prims.list[@@deriving show]
type connective =
  | QAll of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3 
  | QEx of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3 
  | BaseConn of (FStar_Ident.lident,FStar_Syntax_Syntax.args)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____6510 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____6546 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____6580 -> false
  
let (__proj__BaseConn__item___0 :
  connective ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | BaseConn _0 -> _0 
let (destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1  in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____6613) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____6625) ->
          unmeta_monadic t
      | uu____6638 -> f2  in
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
      let aux f2 uu____6716 =
        match uu____6716 with
        | (lid,arity) ->
            let uu____6725 =
              let uu____6740 = unmeta_monadic f2  in head_and_args uu____6740
               in
            (match uu____6725 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____6766 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____6766
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____6841 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____6841)
      | uu____6852 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____6899 = head_and_args t1  in
        match uu____6899 with
        | (t2,args) ->
            let uu____6946 = un_uinst t2  in
            let uu____6947 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6980  ->
                      match uu____6980 with
                      | (t3,imp) ->
                          let uu____6991 = unascribe t3  in (uu____6991, imp)))
               in
            (uu____6946, uu____6947)
         in
      let rec aux qopt out t1 =
        let uu____7026 = let uu____7043 = flat t1  in (qopt, uu____7043)  in
        match uu____7026 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____7070;
                 FStar_Syntax_Syntax.vars = uu____7071;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____7074);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____7075;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____7076;_},uu____7077)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____7154;
                 FStar_Syntax_Syntax.vars = uu____7155;_},uu____7156::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____7159);
                  FStar_Syntax_Syntax.pos = uu____7160;
                  FStar_Syntax_Syntax.vars = uu____7161;_},uu____7162)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7250;
               FStar_Syntax_Syntax.vars = uu____7251;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____7254);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7255;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7256;_},uu____7257)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7333;
               FStar_Syntax_Syntax.vars = uu____7334;_},uu____7335::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____7338);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____7339;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____7340;_},uu____7341)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____7429) ->
            let bs = FStar_List.rev out  in
            let uu____7463 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____7463 with
             | (bs1,t2) ->
                 let uu____7472 = patterns t2  in
                 (match uu____7472 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____7534 -> FStar_Pervasives_Native.None  in
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
      let uu____7600 = un_squash t  in
      FStar_Util.bind_opt uu____7600
        (fun t1  ->
           let uu____7616 = head_and_args' t1  in
           match uu____7616 with
           | (hd1,args) ->
               let uu____7649 =
                 let uu____7654 =
                   let uu____7655 = un_uinst hd1  in
                   uu____7655.FStar_Syntax_Syntax.n  in
                 (uu____7654, (FStar_List.length args))  in
               (match uu____7649 with
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
                | uu____7738 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____7761 = un_squash t  in
      FStar_Util.bind_opt uu____7761
        (fun t1  ->
           let uu____7776 = arrow_one t1  in
           match uu____7776 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____7791 =
                 let uu____7792 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____7792  in
               if uu____7791
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____7799 = comp_to_comp_typ c  in
                    uu____7799.FStar_Syntax_Syntax.result_typ  in
                  let uu____7800 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____7800
                  then
                    let uu____7803 = patterns q  in
                    match uu____7803 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____7859 =
                       let uu____7860 =
                         let uu____7865 =
                           let uu____7868 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____7869 =
                             let uu____7872 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____7872]  in
                           uu____7868 :: uu____7869  in
                         (FStar_Parser_Const.imp_lid, uu____7865)  in
                       BaseConn uu____7860  in
                     FStar_Pervasives_Native.Some uu____7859))
           | uu____7875 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____7883 = un_squash t  in
      FStar_Util.bind_opt uu____7883
        (fun t1  ->
           let uu____7914 = head_and_args' t1  in
           match uu____7914 with
           | (hd1,args) ->
               let uu____7947 =
                 let uu____7960 =
                   let uu____7961 = un_uinst hd1  in
                   uu____7961.FStar_Syntax_Syntax.n  in
                 (uu____7960, args)  in
               (match uu____7947 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____7976)::(a2,uu____7978)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____8013 =
                      let uu____8014 = FStar_Syntax_Subst.compress a2  in
                      uu____8014.FStar_Syntax_Syntax.n  in
                    (match uu____8013 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____8021) ->
                         let uu____8048 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____8048 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____8087 -> failwith "impossible"  in
                              let uu____8092 = patterns q1  in
                              (match uu____8092 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____8159 -> FStar_Pervasives_Native.None)
                | uu____8160 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____8181 = destruct_sq_forall phi  in
          (match uu____8181 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8203 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____8209 = destruct_sq_exists phi  in
          (match uu____8209 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8231 -> f1)
      | uu____8234 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____8238 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____8238
      (fun uu____8243  ->
         let uu____8244 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____8244
           (fun uu____8249  ->
              let uu____8250 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____8250
                (fun uu____8255  ->
                   let uu____8256 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____8256
                     (fun uu____8261  ->
                        let uu____8262 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____8262
                          (fun uu____8266  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____8272 =
      let uu____8273 = FStar_Syntax_Subst.compress t  in
      uu____8273.FStar_Syntax_Syntax.n  in
    match uu____8272 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____8280) ->
        let uu____8307 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____8307 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____8333 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____8333
             then
               let uu____8336 =
                 let uu____8345 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____8345]  in
               mk_app t uu____8336
             else e1)
    | uu____8347 ->
        let uu____8348 =
          let uu____8357 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____8357]  in
        mk_app t uu____8348
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____8365 =
          let uu____8370 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational
              FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____8370  in
        let uu____8371 =
          let uu____8372 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ  in
          arrow a.FStar_Syntax_Syntax.action_params uu____8372  in
        let uu____8375 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
           in
        close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____8365
          a.FStar_Syntax_Syntax.action_univs uu____8371
          FStar_Parser_Const.effect_Tot_lid uu____8375 []
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
    let reify_ =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
       in
    let uu____8402 =
      let uu____8405 =
        let uu____8406 =
          let uu____8421 =
            let uu____8424 = FStar_Syntax_Syntax.as_arg t  in [uu____8424]
             in
          (reify_, uu____8421)  in
        FStar_Syntax_Syntax.Tm_app uu____8406  in
      FStar_Syntax_Syntax.mk uu____8405  in
    uu____8402 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____8436 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____8462 = unfold_lazy i  in delta_qualifier uu____8462
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____8464 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____8465 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____8466 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____8489 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____8506 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____8507 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____8508 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____8522) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____8527;
           FStar_Syntax_Syntax.index = uu____8528;
           FStar_Syntax_Syntax.sort = t2;_},uu____8530)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____8538) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____8544,uu____8545) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8587) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____8608,t2,uu____8610) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____8631,t2) -> delta_qualifier t2
  
let rec (incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth) =
  fun d  ->
    match d with
    | FStar_Syntax_Syntax.Delta_equational  -> d
    | FStar_Syntax_Syntax.Delta_constant  ->
        FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        FStar_Syntax_Syntax.Delta_defined_at_level
          (i + (Prims.parse_int "1"))
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
  
let (incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let uu____8657 = delta_qualifier t  in incr_delta_depth uu____8657
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8661 =
      let uu____8662 = FStar_Syntax_Subst.compress t  in
      uu____8662.FStar_Syntax_Syntax.n  in
    match uu____8661 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____8665 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____8677 = let uu____8692 = unmeta e  in head_and_args uu____8692
       in
    match uu____8677 with
    | (head1,args) ->
        let uu____8719 =
          let uu____8732 =
            let uu____8733 = un_uinst head1  in
            uu____8733.FStar_Syntax_Syntax.n  in
          (uu____8732, args)  in
        (match uu____8719 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____8749) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____8769::(hd1,uu____8771)::(tl1,uu____8773)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____8820 =
               let uu____8825 =
                 let uu____8830 = list_elements tl1  in
                 FStar_Util.must uu____8830  in
               hd1 :: uu____8825  in
             FStar_Pervasives_Native.Some uu____8820
         | uu____8843 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____8861 .
    ('Auu____8861 -> 'Auu____8861) ->
      'Auu____8861 Prims.list -> 'Auu____8861 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____8884 = f a  in [uu____8884]
      | x::xs -> let uu____8889 = apply_last f xs  in x :: uu____8889
  
let (dm4f_lid :
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident) =
  fun ed  ->
    fun name  ->
      let p = FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname  in
      let p' =
        apply_last
          (fun s  ->
             Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))
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
          let uu____8925 =
            let uu____8928 =
              let uu____8929 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____8929  in
            FStar_Syntax_Syntax.mk uu____8928  in
          uu____8925 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____8942 =
            let uu____8943 =
              let uu____8944 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____8944
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____8943 args  in
          uu____8942 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____8956 =
            let uu____8957 =
              let uu____8958 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____8958
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____8957 args  in
          uu____8956 FStar_Pervasives_Native.None pos  in
        let uu____8961 =
          let uu____8962 =
            let uu____8963 = FStar_Syntax_Syntax.iarg typ  in [uu____8963]
             in
          nil uu____8962 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____8969 =
                 let uu____8970 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____8971 =
                   let uu____8974 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____8975 =
                     let uu____8978 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____8978]  in
                   uu____8974 :: uu____8975  in
                 uu____8970 :: uu____8971  in
               cons1 uu____8969 t.FStar_Syntax_Syntax.pos) l uu____8961
  
let (uvar_from_id :
  Prims.int ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun id1  ->
    fun t  ->
      let uu____8987 =
        let uu____8990 =
          let uu____8991 =
            let uu____9008 = FStar_Syntax_Unionfind.from_id id1  in
            (uu____9008, t)  in
          FStar_Syntax_Syntax.Tm_uvar uu____8991  in
        FStar_Syntax_Syntax.mk uu____8990  in
      uu____8987 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        | uu____9068 -> false
  
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
          | uu____9165 -> false
  
let eqprod :
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
        | uu____9303 -> false
  
let rec (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_app uu____9418 ->
            let uu____9433 = head_and_args' t  in
            (match uu____9433 with
             | (hd1,args) ->
                 let uu___58_9466 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.pos =
                     (uu___58_9466.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___58_9466.FStar_Syntax_Syntax.vars)
                 })
        | uu____9477 -> t  in
      let t11 = let uu____9481 = unmeta_safe t1  in canon_app uu____9481  in
      let t21 = let uu____9487 = unmeta_safe t2  in canon_app uu____9487  in
      let uu____9490 =
        let uu____9495 =
          let uu____9496 = FStar_Syntax_Subst.compress t11  in
          uu____9496.FStar_Syntax_Syntax.n  in
        let uu____9499 =
          let uu____9500 = FStar_Syntax_Subst.compress t21  in
          uu____9500.FStar_Syntax_Syntax.n  in
        (uu____9495, uu____9499)  in
      match uu____9490 with
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
      | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
         (b2,c2)) -> (eqlist binder_eq b1 b2) && (comp_eq c1 c2)
      | (FStar_Syntax_Syntax.Tm_refine (b1,t12),FStar_Syntax_Syntax.Tm_refine
         (b2,t22)) -> (FStar_Syntax_Syntax.bv_eq b1 b2) && (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
         (f2,a2)) -> (term_eq f1 f2) && (eqlist arg_eq a1 a2)
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) -> (term_eq t12 t22) && (eqlist branch_eq bs1 bs2)
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12,uu____9768,uu____9769),uu____9770) -> term_eq t12 t21
      | (uu____9811,FStar_Syntax_Syntax.Tm_ascribed
         (t22,uu____9813,uu____9814)) -> term_eq t11 t22
      | (FStar_Syntax_Syntax.Tm_let
         ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
          ((b1 = b2) && (eqlist letbinding_eq lbs1 lbs2)) &&
            (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____9890),FStar_Syntax_Syntax.Tm_uvar (u2,uu____9892)) ->
          u1 = u2
      | (FStar_Syntax_Syntax.Tm_delayed uu____9951,uu____9952) ->
          failwith "impossible: term_eq did not compress properly"
      | (uu____9977,FStar_Syntax_Syntax.Tm_delayed uu____9978) ->
          failwith "impossible: term_eq did not compress properly"
      | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
         (t22,m2)) ->
          (match (m1, m2) with
           | (FStar_Syntax_Syntax.Meta_monadic
              (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
               (FStar_Ident.lid_equals n1 n2) && (term_eq ty1 ty2)
           | (FStar_Syntax_Syntax.Meta_monadic_lift
              (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
              (s2,t23,ty2)) ->
               ((FStar_Ident.lid_equals s1 s2) &&
                  (FStar_Ident.lid_equals t13 t23))
                 && (term_eq ty1 ty2)
           | uu____10041 -> false)
      | (FStar_Syntax_Syntax.Tm_unknown ,FStar_Syntax_Syntax.Tm_unknown ) ->
          false
      | (uu____10046,uu____10047) -> false

and (arg_eq :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun a1  -> fun a2  -> eqprod term_eq (fun q1  -> fun q2  -> q1 = q2) a1 a2

and (binder_eq :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun b1  ->
    fun b2  ->
      eqprod
        (fun b11  ->
           fun b21  ->
             term_eq b11.FStar_Syntax_Syntax.sort
               b21.FStar_Syntax_Syntax.sort) (fun q1  -> fun q2  -> q1 = q2)
        b1 b2

and (lcomp_eq :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c1  -> fun c2  -> false

and (residual_eq :
  FStar_Syntax_Syntax.residual_comp ->
    FStar_Syntax_Syntax.residual_comp -> Prims.bool)
  = fun r1  -> fun r2  -> false

and (comp_eq :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool)
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
      | (uu____10142,uu____10143) -> false

and (eq_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list -> Prims.bool)
  = fun f1  -> fun f2  -> true

and (branch_eq :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax
                                                             FStar_Pervasives_Native.option,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                               FStar_Syntax_Syntax.syntax
                                                               FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 -> Prims.bool)
  =
  fun uu____10150  ->
    fun uu____10151  ->
      match (uu____10150, uu____10151) with
      | ((p1,w1,t1),(p2,w2,t2)) ->
          let uu____10274 = FStar_Syntax_Syntax.eq_pat p1 p2  in
          if uu____10274
          then
            (term_eq t1 t2) &&
              ((match (w1, w2) with
                | (FStar_Pervasives_Native.Some
                   x,FStar_Pervasives_Native.Some y) -> term_eq x y
                | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None
                   ) -> true
                | uu____10315 -> false))
          else false

and (letbinding_eq :
  FStar_Syntax_Syntax.letbinding ->
    FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun lb1  ->
    fun lb2  ->
      (((eqsum FStar_Syntax_Syntax.bv_eq FStar_Syntax_Syntax.fv_eq
           lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname)
          &&
          (lb1.FStar_Syntax_Syntax.lbunivs = lb2.FStar_Syntax_Syntax.lbunivs))
         &&
         (term_eq lb1.FStar_Syntax_Syntax.lbtyp lb2.FStar_Syntax_Syntax.lbtyp))
        &&
        (term_eq lb1.FStar_Syntax_Syntax.lbdef lb2.FStar_Syntax_Syntax.lbdef)

let rec (bottom_fold :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f  in
      let tn =
        let uu____10348 = FStar_Syntax_Subst.compress t  in
        uu____10348.FStar_Syntax_Syntax.n  in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____10374 =
              let uu____10389 = ff f1  in
              let uu____10390 =
                FStar_List.map
                  (fun uu____10409  ->
                     match uu____10409 with
                     | (a,q) -> let uu____10420 = ff a  in (uu____10420, q))
                  args
                 in
              (uu____10389, uu____10390)  in
            FStar_Syntax_Syntax.Tm_app uu____10374
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____10450 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____10450 with
             | (bs1,t') ->
                 let t'' = ff t'  in
                 let uu____10458 =
                   let uu____10475 = FStar_Syntax_Subst.close bs1 t''  in
                   (bs1, uu____10475, k)  in
                 FStar_Syntax_Syntax.Tm_abs uu____10458)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____10502 = let uu____10509 = ff t1  in (uu____10509, us)
               in
            FStar_Syntax_Syntax.Tm_uinst uu____10502
        | uu____10510 -> tn  in
      f
        (let uu___59_10513 = t  in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.pos = (uu___59_10513.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___59_10513.FStar_Syntax_Syntax.vars)
         })
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10517 ->
        let uu____10542 =
          let uu____10543 = FStar_Syntax_Subst.compress t  in
          sizeof uu____10543  in
        (Prims.parse_int "1") + uu____10542
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____10545 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____10545
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____10547 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____10547
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____10554 = sizeof t1  in (FStar_List.length us) + uu____10554
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____10557) ->
        let uu____10578 = sizeof t1  in
        let uu____10579 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____10590  ->
                 match uu____10590 with
                 | (bv,uu____10596) ->
                     let uu____10597 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____10597) (Prims.parse_int "0") bs
           in
        uu____10578 + uu____10579
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____10620 = sizeof hd1  in
        let uu____10621 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____10632  ->
                 match uu____10632 with
                 | (arg,uu____10638) ->
                     let uu____10639 = sizeof arg  in acc + uu____10639)
            (Prims.parse_int "0") args
           in
        uu____10620 + uu____10621
    | uu____10640 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____10647 =
        let uu____10648 = un_uinst t  in uu____10648.FStar_Syntax_Syntax.n
         in
      match uu____10647 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____10652 -> false
  
let (is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  -> is_fvar FStar_Parser_Const.synth_lid t 
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> Prims.unit) =
  fun p  ->
    fun r  ->
      let set_options1 t s =
        let uu____10669 = FStar_Options.set_options t s  in
        match uu____10669 with
        | FStar_Getopt.Success  -> ()
        | FStar_Getopt.Help  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                "Failed to process pragma: use 'fstar --help' to see which options are available")
              r
        | FStar_Getopt.Error s1 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                (Prims.strcat "Failed to process pragma: " s1)) r
         in
      match p with
      | FStar_Syntax_Syntax.LightOff  ->
          if p = FStar_Syntax_Syntax.LightOff
          then FStar_Options.set_ml_ish ()
          else ()
      | FStar_Syntax_Syntax.SetOptions o -> set_options1 FStar_Options.Set o
      | FStar_Syntax_Syntax.ResetOptions sopt ->
          ((let uu____10677 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____10677 FStar_Pervasives.ignore);
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
  