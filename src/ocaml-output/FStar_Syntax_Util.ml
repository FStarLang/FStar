open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____27 = FStar_ST.op_Bang tts_f  in
    match uu____27 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____72 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____72 id1.FStar_Ident.idRange
  
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
  'Auu____82 .
    (FStar_Syntax_Syntax.bv,'Auu____82) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term,'Auu____82) FStar_Pervasives_Native.tuple2
  =
  fun uu____94  ->
    match uu____94 with
    | (b,imp) ->
        let uu____101 = FStar_Syntax_Syntax.bv_to_name b  in (uu____101, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____124 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____124
            then []
            else (let uu____136 = arg_of_non_null_binder b  in [uu____136])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  =
  fun binders  ->
    let uu____160 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____206 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____206
              then
                let b1 =
                  let uu____224 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____224, (FStar_Pervasives_Native.snd b))  in
                let uu____225 = arg_of_non_null_binder b1  in (b1, uu____225)
              else
                (let uu____239 = arg_of_non_null_binder b  in (b, uu____239))))
       in
    FStar_All.pipe_right uu____160 FStar_List.unzip
  
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
              let uu____321 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____321
              then
                let uu____326 = b  in
                match uu____326 with
                | (a,imp) ->
                    let b1 =
                      let uu____334 =
                        let uu____335 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____335  in
                      FStar_Ident.id_of_text uu____334  in
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
        let uu____367 =
          let uu____370 =
            let uu____371 =
              let uu____384 = name_binders binders  in (uu____384, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____371  in
          FStar_Syntax_Syntax.mk uu____370  in
        uu____367 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____402 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____442  ->
            match uu____442 with
            | (t,imp) ->
                let uu____453 =
                  let uu____454 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____454
                   in
                (uu____453, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____504  ->
            match uu____504 with
            | (t,imp) ->
                let uu____521 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____521, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____531 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____531
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____540 . 'Auu____540 -> 'Auu____540 Prims.list =
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
          (fun uu____627  ->
             fun uu____628  ->
               match (uu____627, uu____628) with
               | ((x,uu____646),(y,uu____648)) ->
                   let uu____657 =
                     let uu____664 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____664)  in
                   FStar_Syntax_Syntax.NT uu____657) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        (uu____670,FStar_Syntax_Syntax.Meta_quoted uu____671) -> e1
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____683) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____689,uu____690) -> unmeta e2
    | uu____731 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____742 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____749 -> e1
         | FStar_Syntax_Syntax.Meta_quoted uu____758 -> e1
         | uu____765 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____767,uu____768) ->
        unmeta_safe e2
    | uu____809 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____821 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____822 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____832 = univ_kernel u1  in
        (match uu____832 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____843 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____850 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____858 = univ_kernel u  in FStar_Pervasives_Native.snd uu____858
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____869,uu____870) ->
          failwith "Impossible: compare_univs"
      | (uu____871,FStar_Syntax_Syntax.U_bvar uu____872) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____873) ->
          ~- (Prims.parse_int "1")
      | (uu____874,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____875) -> ~- (Prims.parse_int "1")
      | (uu____876,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____879,FStar_Syntax_Syntax.U_unif
         uu____880) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____889,FStar_Syntax_Syntax.U_name
         uu____890) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____917 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____918 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____917 - uu____918
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____949 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____949
                 (fun uu____964  ->
                    match uu____964 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____978,uu____979) ->
          ~- (Prims.parse_int "1")
      | (uu____982,FStar_Syntax_Syntax.U_max uu____983) ->
          (Prims.parse_int "1")
      | uu____986 ->
          let uu____991 = univ_kernel u1  in
          (match uu____991 with
           | (k1,n1) ->
               let uu____998 = univ_kernel u2  in
               (match uu____998 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1013 = compare_univs u1 u2  in
      uu____1013 = (Prims.parse_int "0")
  
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
    | FStar_Syntax_Syntax.Total uu____1038 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1047 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1067 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1076 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1100 =
          let uu____1101 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1101  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1100;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1128 =
          let uu____1129 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1129  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1128;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
  
let (comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    fun f  ->
      let uu___50_1158 = c  in
      let uu____1159 =
        let uu____1160 =
          let uu___51_1161 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___51_1161.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___51_1161.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___51_1161.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___51_1161.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1160  in
      {
        FStar_Syntax_Syntax.n = uu____1159;
        FStar_Syntax_Syntax.pos = (uu___50_1158.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___50_1158.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1176 -> c
        | FStar_Syntax_Syntax.GTotal uu____1185 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___52_1196 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___52_1196.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___52_1196.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___52_1196.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___52_1196.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___53_1197 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___53_1197.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___53_1197.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1200  ->
           let uu____1201 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1201)
  
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
    | uu____1234 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1243 -> true
    | FStar_Syntax_Syntax.GTotal uu____1252 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___38_1271  ->
               match uu___38_1271 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1272 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___39_1279  ->
               match uu___39_1279 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1280 -> false)))
  
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
            (fun uu___40_1287  ->
               match uu___40_1287 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1288 -> false)))
  
let (is_tac_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
      FStar_Parser_Const.effect_Tac_lid
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___41_1302  ->
            match uu___41_1302 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1303 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___42_1310  ->
            match uu___42_1310 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1311 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1336 -> true
    | FStar_Syntax_Syntax.GTotal uu____1345 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___43_1358  ->
                   match uu___43_1358 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1359 -> false)))
  
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
            (fun uu___44_1376  ->
               match uu___44_1376 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1377 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1384 =
      let uu____1385 = FStar_Syntax_Subst.compress t  in
      uu____1385.FStar_Syntax_Syntax.n  in
    match uu____1384 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1388,c) -> is_pure_or_ghost_comp c
    | uu____1406 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1415 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1419 =
      let uu____1420 = FStar_Syntax_Subst.compress t  in
      uu____1420.FStar_Syntax_Syntax.n  in
    match uu____1419 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1423,c) -> is_lemma_comp c
    | uu____1441 -> false
  
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
    | uu____1506 -> (t1, [])
  
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
        let uu____1571 = head_and_args' head1  in
        (match uu____1571 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1628 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1648) ->
        FStar_Syntax_Subst.compress t2
    | uu____1653 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1657 =
      let uu____1658 = FStar_Syntax_Subst.compress t  in
      uu____1658.FStar_Syntax_Syntax.n  in
    match uu____1657 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1661,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1683)::uu____1684 ->
                  let pats' = unmeta pats  in
                  let uu____1728 = head_and_args pats'  in
                  (match uu____1728 with
                   | (head1,uu____1744) ->
                       let uu____1765 =
                         let uu____1766 = un_uinst head1  in
                         uu____1766.FStar_Syntax_Syntax.n  in
                       (match uu____1765 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1770 -> false))
              | uu____1771 -> false)
         | uu____1780 -> false)
    | uu____1781 -> false
  
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
                (fun uu___45_1793  ->
                   match uu___45_1793 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1794 -> false)))
    | uu____1795 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1808) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1818) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____1838 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____1847 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___54_1859 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___54_1859.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___54_1859.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___54_1859.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___54_1859.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___46_1870  ->
            match uu___46_1870 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____1871 -> false))
  
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
    | uu____1887 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1893,uu____1894) ->
        unascribe e2
    | uu____1935 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1983,uu____1984) ->
          ascribe t' k
      | uu____2025 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2049 =
      let uu____2054 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2054  in
    uu____2049 i.FStar_Syntax_Syntax.kind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2099 =
      let uu____2100 = FStar_Syntax_Subst.compress t  in
      uu____2100.FStar_Syntax_Syntax.n  in
    match uu____2099 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2104 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2104
    | uu____2105 -> t
  
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
            let uu____2135 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2135;
              FStar_Syntax_Syntax.kind = k;
              FStar_Syntax_Syntax.typ = typ;
              FStar_Syntax_Syntax.rng = rng
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i)
            FStar_Pervasives_Native.None rng
  
let (canon_app :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____2141 =
      let uu____2154 = unascribe t  in head_and_args' uu____2154  in
    match uu____2141 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown [@@deriving show]
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2178 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2182 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2186 -> false
  
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
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___47_2244 = if uu___47_2244 then Equal else Unknown  in
      let equal_iff uu___48_2249 = if uu___48_2249 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2263 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2271) -> NotEqual
        | (uu____2272,NotEqual ) -> NotEqual
        | (Unknown ,uu____2273) -> Unknown
        | (uu____2274,Unknown ) -> Unknown  in
      let notq t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (uu____2283,FStar_Syntax_Syntax.Meta_quoted uu____2284) -> false
        | uu____2295 -> true  in
      let equal_data f1 args1 f2 args2 =
        let uu____2333 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2333
        then
          let uu____2337 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2395  ->
                    match uu____2395 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2423 = eq_tm a1 a2  in
                        eq_inj acc uu____2423) Equal) uu____2337
        else NotEqual  in
      let uu____2425 =
        let uu____2430 =
          let uu____2431 = FStar_Syntax_Subst.compress t11  in
          uu____2431.FStar_Syntax_Syntax.n  in
        let uu____2434 =
          let uu____2435 = FStar_Syntax_Subst.compress t21  in
          uu____2435.FStar_Syntax_Syntax.n  in
        (uu____2430, uu____2434)  in
      match uu____2425 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2440,uu____2441) ->
          let uu____2442 = unlazy t11  in eq_tm uu____2442 t21
      | (uu____2443,FStar_Syntax_Syntax.Tm_lazy uu____2444) ->
          let uu____2445 = unlazy t21  in eq_tm t11 uu____2445
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
            (let uu____2463 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2463)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2476 = eq_tm f g  in
          eq_and uu____2476
            (fun uu____2479  ->
               let uu____2480 = eq_univs_list us vs  in equal_if uu____2480)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2481),uu____2482) -> Unknown
      | (uu____2483,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2484)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2487 = FStar_Const.eq_const c d  in equal_iff uu____2487
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2489),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2491)) ->
          let uu____2540 = FStar_Syntax_Unionfind.equiv u1 u2  in
          equal_if uu____2540
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2585 =
            let uu____2590 =
              let uu____2591 = un_uinst h1  in
              uu____2591.FStar_Syntax_Syntax.n  in
            let uu____2594 =
              let uu____2595 = un_uinst h2  in
              uu____2595.FStar_Syntax_Syntax.n  in
            (uu____2590, uu____2594)  in
          (match uu____2585 with
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
                 (let uu____2607 =
                    let uu____2608 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____2608  in
                  FStar_List.mem uu____2607 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____2609 ->
               let uu____2614 = eq_tm h1 h2  in
               eq_and uu____2614 (fun uu____2616  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____2721 = FStar_List.zip bs1 bs2  in
            let uu____2784 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____2821  ->
                 fun a  ->
                   match uu____2821 with
                   | (b1,b2) ->
                       eq_and a (fun uu____2914  -> branch_matches b1 b2))
              uu____2721 uu____2784
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____2918 = eq_univs u v1  in equal_if uu____2918
      | (FStar_Syntax_Syntax.Tm_meta (t1',uu____2920),uu____2921) when
          notq t11 -> eq_tm t1' t21
      | (uu____2926,FStar_Syntax_Syntax.Tm_meta (t2',uu____2928)) when
          notq t21 -> eq_tm t11 t2'
      | (FStar_Syntax_Syntax.Tm_meta
         (uu____2933,FStar_Syntax_Syntax.Meta_quoted (t12,uu____2935)),FStar_Syntax_Syntax.Tm_meta
         (uu____2936,FStar_Syntax_Syntax.Meta_quoted (t22,uu____2938))) ->
          eq_tm t12 t22
      | uu____2955 -> Unknown

and (branch_matches :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax
                                                             FStar_Pervasives_Native.option,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                               FStar_Syntax_Syntax.syntax
                                                               FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 -> eq_result)
  =
  fun b1  ->
    fun b2  ->
      let related_by f o1 o2 =
        match (o1, o2) with
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            true
        | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y) ->
            f x y
        | (uu____3032,uu____3033) -> false  in
      let uu____3042 = b1  in
      match uu____3042 with
      | (p1,w1,t1) ->
          let uu____3076 = b2  in
          (match uu____3076 with
           | (p2,w2,t2) ->
               let uu____3110 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3110
               then
                 let uu____3111 =
                   (let uu____3114 = eq_tm t1 t2  in uu____3114 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3123 = eq_tm t11 t21  in
                             uu____3123 = Equal) w1 w2)
                    in
                 (if uu____3111 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3157)::a11,(b,uu____3160)::b1) ->
          let uu____3214 = eq_tm a b  in
          (match uu____3214 with
           | Equal  -> eq_args a11 b1
           | uu____3215 -> Unknown)
      | uu____3216 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3228) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3234,uu____3235) ->
        unrefine t2
    | uu____3276 -> t1
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3280 =
      let uu____3281 = unrefine t  in uu____3281.FStar_Syntax_Syntax.n  in
    match uu____3280 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3286) -> is_unit t1
    | uu____3291 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3295 =
      let uu____3296 = unrefine t  in uu____3296.FStar_Syntax_Syntax.n  in
    match uu____3295 with
    | FStar_Syntax_Syntax.Tm_type uu____3299 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3302) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3324) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3329,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3347 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____3351 =
      let uu____3352 = FStar_Syntax_Subst.compress e  in
      uu____3352.FStar_Syntax_Syntax.n  in
    match uu____3351 with
    | FStar_Syntax_Syntax.Tm_abs uu____3355 -> true
    | uu____3372 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3376 =
      let uu____3377 = FStar_Syntax_Subst.compress t  in
      uu____3377.FStar_Syntax_Syntax.n  in
    match uu____3376 with
    | FStar_Syntax_Syntax.Tm_arrow uu____3380 -> true
    | uu____3393 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3399) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3405,uu____3406) ->
        pre_typ t2
    | uu____3447 -> t1
  
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
      let uu____3465 =
        let uu____3466 = un_uinst typ1  in uu____3466.FStar_Syntax_Syntax.n
         in
      match uu____3465 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____3521 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____3545 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____3561,lids) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____3567,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3578,uu____3579,uu____3580,uu____3581,uu____3582) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____3592,uu____3593,uu____3594,uu____3595) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____3601,uu____3602,uu____3603,uu____3604,uu____3605) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3611,uu____3612) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3614,uu____3615) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3618 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____3619 -> []
    | FStar_Syntax_Syntax.Sig_main uu____3620 -> []
    | FStar_Syntax_Syntax.Sig_splice uu____3621 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____3632 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___49_3649  ->
    match uu___49_3649 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____3659 'Auu____3660 .
    ('Auu____3659 FStar_Syntax_Syntax.syntax,'Auu____3660)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____3670  ->
    match uu____3670 with | (hd1,uu____3678) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____3687 'Auu____3688 .
    ('Auu____3687 FStar_Syntax_Syntax.syntax,'Auu____3688)
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
      FStar_Syntax_Syntax.term FStar_Syntax_Syntax.syntax)
  =
  fun l  ->
    fun args  ->
      match args with
      | [] ->
          let uu____3808 =
            let uu____3811 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____3811  in
          uu____3808 FStar_Pervasives_Native.None
            (FStar_Ident.range_of_lid l)
      | uu____3815 ->
          let e =
            let uu____3827 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____3827 args  in
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
  
let (mangle_field_name : FStar_Ident.ident -> FStar_Ident.ident) =
  fun x  ->
    FStar_Ident.mk_ident
      ((Prims.strcat "__fname__" x.FStar_Ident.idText),
        (x.FStar_Ident.idRange))
  
let (unmangle_field_name : FStar_Ident.ident -> FStar_Ident.ident) =
  fun x  ->
    if FStar_Util.starts_with x.FStar_Ident.idText "__fname__"
    then
      let uu____3838 =
        let uu____3843 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____3843, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____3838
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
          let uu____3878 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____3878
          then
            let uu____3879 =
              let uu____3884 =
                let uu____3885 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____3885  in
              let uu____3886 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____3884, uu____3886)  in
            FStar_Ident.mk_ident uu____3879
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___55_3889 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___55_3889.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___55_3889.FStar_Syntax_Syntax.sort)
          }  in
        let uu____3890 = mk_field_projector_name_from_ident lid nm  in
        (uu____3890, y)
  
let (set_uvar :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit) =
  fun uv  ->
    fun t  ->
      let uu____3897 = FStar_Syntax_Unionfind.find uv  in
      match uu____3897 with
      | FStar_Pervasives_Native.Some uu____3900 ->
          let uu____3901 =
            let uu____3902 =
              let uu____3903 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____3903  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3902  in
          failwith uu____3901
      | uu____3904 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____3975 -> q1 = q2
  
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
              let uu____4006 =
                let uu___56_4007 = rc  in
                let uu____4008 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___56_4007.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____4008;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___56_4007.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____4006
           in
        match bs with
        | [] -> t
        | uu____4019 ->
            let body =
              let uu____4021 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4021  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4049 =
                   let uu____4052 =
                     let uu____4053 =
                       let uu____4070 =
                         let uu____4077 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4077 bs'  in
                       let uu____4088 = close_lopt lopt'  in
                       (uu____4070, t1, uu____4088)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4053  in
                   FStar_Syntax_Syntax.mk uu____4052  in
                 uu____4049 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4104 ->
                 let uu____4111 =
                   let uu____4114 =
                     let uu____4115 =
                       let uu____4132 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4133 = close_lopt lopt  in
                       (uu____4132, body, uu____4133)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4115  in
                   FStar_Syntax_Syntax.mk uu____4114  in
                 uu____4111 FStar_Pervasives_Native.None
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
      | uu____4171 ->
          let uu____4178 =
            let uu____4181 =
              let uu____4182 =
                let uu____4195 = FStar_Syntax_Subst.close_binders bs  in
                let uu____4196 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____4195, uu____4196)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4182  in
            FStar_Syntax_Syntax.mk uu____4181  in
          uu____4178 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____4227 =
        let uu____4228 = FStar_Syntax_Subst.compress t  in
        uu____4228.FStar_Syntax_Syntax.n  in
      match uu____4227 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____4254) ->
               let uu____4263 =
                 let uu____4264 = FStar_Syntax_Subst.compress tres  in
                 uu____4264.FStar_Syntax_Syntax.n  in
               (match uu____4263 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____4299 -> t)
           | uu____4300 -> t)
      | uu____4301 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____4310 =
        let uu____4311 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____4311 t.FStar_Syntax_Syntax.pos  in
      let uu____4312 =
        let uu____4315 =
          let uu____4316 =
            let uu____4323 =
              let uu____4324 =
                let uu____4325 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____4325]  in
              FStar_Syntax_Subst.close uu____4324 t  in
            (b, uu____4323)  in
          FStar_Syntax_Syntax.Tm_refine uu____4316  in
        FStar_Syntax_Syntax.mk uu____4315  in
      uu____4312 FStar_Pervasives_Native.None uu____4310
  
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
        let uu____4374 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____4374 with
         | (bs1,c1) ->
             let uu____4391 = is_tot_or_gtot_comp c1  in
             if uu____4391
             then
               let uu____4402 = arrow_formals_comp (comp_result c1)  in
               (match uu____4402 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____4448;
           FStar_Syntax_Syntax.index = uu____4449;
           FStar_Syntax_Syntax.sort = k2;_},uu____4451)
        -> arrow_formals_comp k2
    | uu____4458 ->
        let uu____4459 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4459)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____4485 = arrow_formals_comp k  in
    match uu____4485 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____4561 =
            let uu___57_4562 = rc  in
            let uu____4563 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___57_4562.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____4563;
              FStar_Syntax_Syntax.residual_flags =
                (uu___57_4562.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____4561
      | uu____4570 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____4598 =
        let uu____4599 =
          let uu____4602 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____4602  in
        uu____4599.FStar_Syntax_Syntax.n  in
      match uu____4598 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____4640 = aux t2 what  in
          (match uu____4640 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____4700 -> ([], t1, abs_body_lcomp)  in
    let uu____4713 = aux t FStar_Pervasives_Native.None  in
    match uu____4713 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____4755 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____4755 with
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
      FStar_Ident.ident Prims.list ->
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
                    | (FStar_Pervasives_Native.None ,uu____4886) -> def
                    | (uu____4897,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____4909) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _0_27  ->
                                  FStar_Syntax_Syntax.U_name _0_27))
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
            let uu____5009 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____5009 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5038 ->
            let t' = arrow binders c  in
            let uu____5048 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5048 with
             | (uvs1,t'1) ->
                 let uu____5067 =
                   let uu____5068 = FStar_Syntax_Subst.compress t'1  in
                   uu____5068.FStar_Syntax_Syntax.n  in
                 (match uu____5067 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____5109 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____5126 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____5131 -> false
  
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
      let uu____5163 =
        let uu____5164 = pre_typ t  in uu____5164.FStar_Syntax_Syntax.n  in
      match uu____5163 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____5168 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____5175 =
        let uu____5176 = pre_typ t  in uu____5176.FStar_Syntax_Syntax.n  in
      match uu____5175 with
      | FStar_Syntax_Syntax.Tm_fvar uu____5179 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____5181) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5203) ->
          is_constructed_typ t1 lid
      | uu____5208 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____5217 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____5218 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____5219 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5221) -> get_tycon t2
    | uu____5242 -> FStar_Pervasives_Native.None
  
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
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5252 =
      let uu____5253 = un_uinst t  in uu____5253.FStar_Syntax_Syntax.n  in
    match uu____5252 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____5257 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____5264 =
        let uu____5267 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____5267  in
      match uu____5264 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____5280 -> false
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
  fun uu____5294  ->
    let u =
      let uu____5300 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_28  -> FStar_Syntax_Syntax.U_unif _0_28)
        uu____5300
       in
    let uu____5317 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____5317, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____5328 = eq_tm a a'  in
      match uu____5328 with | Equal  -> true | uu____5329 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____5332 =
    let uu____5335 =
      let uu____5336 =
        let uu____5337 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____5337
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____5336  in
    FStar_Syntax_Syntax.mk uu____5335  in
  uu____5332 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
let (b2t_v : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.b2t_lid 
let (t_not : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.not_lid 
let (t_false : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.false_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (t_true : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (tac_opaque_attr : FStar_Syntax_Syntax.term) = exp_string "tac_opaque" 
let (dm4f_bind_range_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.dm4f_bind_range_attr 
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
          let uu____5384 =
            let uu____5387 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____5388 =
              let uu____5391 =
                let uu____5392 =
                  let uu____5407 =
                    let uu____5410 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____5411 =
                      let uu____5414 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____5414]  in
                    uu____5410 :: uu____5411  in
                  (tand, uu____5407)  in
                FStar_Syntax_Syntax.Tm_app uu____5392  in
              FStar_Syntax_Syntax.mk uu____5391  in
            uu____5388 FStar_Pervasives_Native.None uu____5387  in
          FStar_Pervasives_Native.Some uu____5384
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____5437 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____5438 =
          let uu____5441 =
            let uu____5442 =
              let uu____5457 =
                let uu____5460 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____5461 =
                  let uu____5464 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____5464]  in
                uu____5460 :: uu____5461  in
              (op_t, uu____5457)  in
            FStar_Syntax_Syntax.Tm_app uu____5442  in
          FStar_Syntax_Syntax.mk uu____5441  in
        uu____5438 FStar_Pervasives_Native.None uu____5437
  
let (mk_neg :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____5477 =
      let uu____5480 =
        let uu____5481 =
          let uu____5496 =
            let uu____5499 = FStar_Syntax_Syntax.as_arg phi  in [uu____5499]
             in
          (t_not, uu____5496)  in
        FStar_Syntax_Syntax.Tm_app uu____5481  in
      FStar_Syntax_Syntax.mk uu____5480  in
    uu____5477 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____5560 =
      let uu____5563 =
        let uu____5564 =
          let uu____5579 =
            let uu____5582 = FStar_Syntax_Syntax.as_arg e  in [uu____5582]
             in
          (b2t_v, uu____5579)  in
        FStar_Syntax_Syntax.Tm_app uu____5564  in
      FStar_Syntax_Syntax.mk uu____5563  in
    uu____5560 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____5596 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____5597 =
        let uu____5600 =
          let uu____5601 =
            let uu____5616 =
              let uu____5619 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____5620 =
                let uu____5623 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____5623]  in
              uu____5619 :: uu____5620  in
            (teq, uu____5616)  in
          FStar_Syntax_Syntax.Tm_app uu____5601  in
        FStar_Syntax_Syntax.mk uu____5600  in
      uu____5597 FStar_Pervasives_Native.None uu____5596
  
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
          let uu____5642 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____5643 =
            let uu____5646 =
              let uu____5647 =
                let uu____5662 =
                  let uu____5665 = FStar_Syntax_Syntax.iarg t  in
                  let uu____5666 =
                    let uu____5669 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____5670 =
                      let uu____5673 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____5673]  in
                    uu____5669 :: uu____5670  in
                  uu____5665 :: uu____5666  in
                (eq_inst, uu____5662)  in
              FStar_Syntax_Syntax.Tm_app uu____5647  in
            FStar_Syntax_Syntax.mk uu____5646  in
          uu____5643 FStar_Pervasives_Native.None uu____5642
  
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
        let uu____5696 =
          let uu____5699 =
            let uu____5700 =
              let uu____5715 =
                let uu____5718 = FStar_Syntax_Syntax.iarg t  in
                let uu____5719 =
                  let uu____5722 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____5723 =
                    let uu____5726 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____5726]  in
                  uu____5722 :: uu____5723  in
                uu____5718 :: uu____5719  in
              (t_has_type1, uu____5715)  in
            FStar_Syntax_Syntax.Tm_app uu____5700  in
          FStar_Syntax_Syntax.mk uu____5699  in
        uu____5696 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____5751 =
          let uu____5754 =
            let uu____5755 =
              let uu____5770 =
                let uu____5773 = FStar_Syntax_Syntax.iarg t  in
                let uu____5774 =
                  let uu____5777 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____5777]  in
                uu____5773 :: uu____5774  in
              (t_with_type1, uu____5770)  in
            FStar_Syntax_Syntax.Tm_app uu____5755  in
          FStar_Syntax_Syntax.mk uu____5754  in
        uu____5751 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu____5787 =
    let uu____5790 =
      let uu____5791 =
        let uu____5798 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____5798, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____5791  in
    FStar_Syntax_Syntax.mk uu____5790  in
  uu____5787 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____5811 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____5824 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____5835 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____5811 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____5856  -> c0)
  
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
        let uu____5912 =
          let uu____5915 =
            let uu____5916 =
              let uu____5931 =
                let uu____5934 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____5935 =
                  let uu____5938 =
                    let uu____5939 =
                      let uu____5940 =
                        let uu____5941 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____5941]  in
                      abs uu____5940 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____5939  in
                  [uu____5938]  in
                uu____5934 :: uu____5935  in
              (fa, uu____5931)  in
            FStar_Syntax_Syntax.Tm_app uu____5916  in
          FStar_Syntax_Syntax.mk uu____5915  in
        uu____5912 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____5980 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____5980
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____5989 -> true
    | uu____5990 -> false
  
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
          let uu____6029 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____6029, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____6057 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____6057, FStar_Pervasives_Native.None, t2)  in
        let uu____6070 =
          let uu____6071 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____6071  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____6070
  
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
      let uu____6141 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6144 =
        let uu____6153 = FStar_Syntax_Syntax.as_arg p  in [uu____6153]  in
      mk_app uu____6141 uu____6144
  
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
      let uu____6163 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6166 =
        let uu____6175 = FStar_Syntax_Syntax.as_arg p  in [uu____6175]  in
      mk_app uu____6163 uu____6166
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6183 = head_and_args t  in
    match uu____6183 with
    | (head1,args) ->
        let uu____6224 =
          let uu____6237 =
            let uu____6238 = un_uinst head1  in
            uu____6238.FStar_Syntax_Syntax.n  in
          (uu____6237, args)  in
        (match uu____6224 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____6255)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____6307 =
                    let uu____6312 =
                      let uu____6313 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____6313]  in
                    FStar_Syntax_Subst.open_term uu____6312 p  in
                  (match uu____6307 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____6342 -> failwith "impossible"  in
                       let uu____6347 =
                         let uu____6348 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____6348
                          in
                       if uu____6347
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____6358 -> FStar_Pervasives_Native.None)
         | uu____6361 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6387 = head_and_args t  in
    match uu____6387 with
    | (head1,args) ->
        let uu____6432 =
          let uu____6445 =
            let uu____6446 = FStar_Syntax_Subst.compress head1  in
            uu____6446.FStar_Syntax_Syntax.n  in
          (uu____6445, args)  in
        (match uu____6432 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____6466;
               FStar_Syntax_Syntax.vars = uu____6467;_},u::[]),(t1,uu____6470)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____6509 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6539 = head_and_args t  in
    match uu____6539 with
    | (head1,args) ->
        let uu____6584 =
          let uu____6597 =
            let uu____6598 = FStar_Syntax_Subst.compress head1  in
            uu____6598.FStar_Syntax_Syntax.n  in
          (uu____6597, args)  in
        (match uu____6584 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____6618;
               FStar_Syntax_Syntax.vars = uu____6619;_},u::[]),(t1,uu____6622)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____6661 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____6683 = let uu____6698 = unmeta t  in head_and_args uu____6698
       in
    match uu____6683 with
    | (head1,uu____6700) ->
        let uu____6721 =
          let uu____6722 = un_uinst head1  in
          uu____6722.FStar_Syntax_Syntax.n  in
        (match uu____6721 with
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
         | uu____6726 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6742 =
      let uu____6755 =
        let uu____6756 = FStar_Syntax_Subst.compress t  in
        uu____6756.FStar_Syntax_Syntax.n  in
      match uu____6755 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____6865 =
            let uu____6874 =
              let uu____6875 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____6875  in
            (b, uu____6874)  in
          FStar_Pervasives_Native.Some uu____6865
      | uu____6888 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____6742
      (fun uu____6924  ->
         match uu____6924 with
         | (b,c) ->
             let uu____6959 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____6959 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____7006 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____7029 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____7029
  
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
    match projectee with | QAll _0 -> true | uu____7072 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____7108 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____7142 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____7175) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____7187) ->
          unmeta_monadic t
      | uu____7200 -> f2  in
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
      let aux f2 uu____7278 =
        match uu____7278 with
        | (lid,arity) ->
            let uu____7287 =
              let uu____7302 = unmeta_monadic f2  in head_and_args uu____7302
               in
            (match uu____7287 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____7328 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____7328
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____7403 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____7403)
      | uu____7414 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____7461 = head_and_args t1  in
        match uu____7461 with
        | (t2,args) ->
            let uu____7508 = un_uinst t2  in
            let uu____7509 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____7542  ->
                      match uu____7542 with
                      | (t3,imp) ->
                          let uu____7553 = unascribe t3  in (uu____7553, imp)))
               in
            (uu____7508, uu____7509)
         in
      let rec aux qopt out t1 =
        let uu____7588 = let uu____7605 = flat t1  in (qopt, uu____7605)  in
        match uu____7588 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____7632;
                 FStar_Syntax_Syntax.vars = uu____7633;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____7636);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____7637;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____7638;_},uu____7639)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____7716;
                 FStar_Syntax_Syntax.vars = uu____7717;_},uu____7718::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____7721);
                  FStar_Syntax_Syntax.pos = uu____7722;
                  FStar_Syntax_Syntax.vars = uu____7723;_},uu____7724)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7812;
               FStar_Syntax_Syntax.vars = uu____7813;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____7816);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7817;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7818;_},uu____7819)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7895;
               FStar_Syntax_Syntax.vars = uu____7896;_},uu____7897::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____7900);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____7901;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____7902;_},uu____7903)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____7991) ->
            let bs = FStar_List.rev out  in
            let uu____8025 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____8025 with
             | (bs1,t2) ->
                 let uu____8034 = patterns t2  in
                 (match uu____8034 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____8096 -> FStar_Pervasives_Native.None  in
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
      let uu____8162 = un_squash t  in
      FStar_Util.bind_opt uu____8162
        (fun t1  ->
           let uu____8178 = head_and_args' t1  in
           match uu____8178 with
           | (hd1,args) ->
               let uu____8211 =
                 let uu____8216 =
                   let uu____8217 = un_uinst hd1  in
                   uu____8217.FStar_Syntax_Syntax.n  in
                 (uu____8216, (FStar_List.length args))  in
               (match uu____8211 with
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
                | uu____8300 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____8323 = un_squash t  in
      FStar_Util.bind_opt uu____8323
        (fun t1  ->
           let uu____8338 = arrow_one t1  in
           match uu____8338 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____8353 =
                 let uu____8354 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____8354  in
               if uu____8353
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____8361 = comp_to_comp_typ c  in
                    uu____8361.FStar_Syntax_Syntax.result_typ  in
                  let uu____8362 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____8362
                  then
                    let uu____8365 = patterns q  in
                    match uu____8365 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____8421 =
                       let uu____8422 =
                         let uu____8427 =
                           let uu____8430 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____8431 =
                             let uu____8434 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____8434]  in
                           uu____8430 :: uu____8431  in
                         (FStar_Parser_Const.imp_lid, uu____8427)  in
                       BaseConn uu____8422  in
                     FStar_Pervasives_Native.Some uu____8421))
           | uu____8437 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____8445 = un_squash t  in
      FStar_Util.bind_opt uu____8445
        (fun t1  ->
           let uu____8476 = head_and_args' t1  in
           match uu____8476 with
           | (hd1,args) ->
               let uu____8509 =
                 let uu____8522 =
                   let uu____8523 = un_uinst hd1  in
                   uu____8523.FStar_Syntax_Syntax.n  in
                 (uu____8522, args)  in
               (match uu____8509 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____8538)::(a2,uu____8540)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____8575 =
                      let uu____8576 = FStar_Syntax_Subst.compress a2  in
                      uu____8576.FStar_Syntax_Syntax.n  in
                    (match uu____8575 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____8583) ->
                         let uu____8610 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____8610 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____8649 -> failwith "impossible"  in
                              let uu____8654 = patterns q1  in
                              (match uu____8654 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____8721 -> FStar_Pervasives_Native.None)
                | uu____8722 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____8743 = destruct_sq_forall phi  in
          (match uu____8743 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8765 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____8771 = destruct_sq_exists phi  in
          (match uu____8771 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8793 -> f1)
      | uu____8796 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____8800 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____8800
      (fun uu____8805  ->
         let uu____8806 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____8806
           (fun uu____8811  ->
              let uu____8812 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____8812
                (fun uu____8817  ->
                   let uu____8818 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____8818
                     (fun uu____8823  ->
                        let uu____8824 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____8824
                          (fun uu____8828  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____8834 =
      let uu____8835 = FStar_Syntax_Subst.compress t  in
      uu____8835.FStar_Syntax_Syntax.n  in
    match uu____8834 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____8842) ->
        let uu____8869 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____8869 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____8895 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____8895
             then
               let uu____8898 =
                 let uu____8907 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____8907]  in
               mk_app t uu____8898
             else e1)
    | uu____8909 ->
        let uu____8910 =
          let uu____8919 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____8919]  in
        mk_app t uu____8910
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____8930 =
            let uu____8935 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.Delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____8935  in
          let uu____8936 =
            let uu____8937 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____8937  in
          let uu____8940 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____8930 a.FStar_Syntax_Syntax.action_univs uu____8936
            FStar_Parser_Const.effect_Tot_lid uu____8940 [] pos
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
    let uu____8967 =
      let uu____8970 =
        let uu____8971 =
          let uu____8986 =
            let uu____8989 = FStar_Syntax_Syntax.as_arg t  in [uu____8989]
             in
          (reify_, uu____8986)  in
        FStar_Syntax_Syntax.Tm_app uu____8971  in
      FStar_Syntax_Syntax.mk uu____8970  in
    uu____8967 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____9001 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____9027 = unfold_lazy i  in delta_qualifier uu____9027
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____9029 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____9030 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____9031 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____9054 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____9071 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____9072 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____9073 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____9087) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____9092;
           FStar_Syntax_Syntax.index = uu____9093;
           FStar_Syntax_Syntax.sort = t2;_},uu____9095)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____9103) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____9109,uu____9110) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____9152) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____9173,t2,uu____9175) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____9196,t2) -> delta_qualifier t2
  
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
    let uu____9222 = delta_qualifier t  in incr_delta_depth uu____9222
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9226 =
      let uu____9227 = FStar_Syntax_Subst.compress t  in
      uu____9227.FStar_Syntax_Syntax.n  in
    match uu____9226 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____9230 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9242 = let uu____9257 = unmeta e  in head_and_args uu____9257
       in
    match uu____9242 with
    | (head1,args) ->
        let uu____9284 =
          let uu____9297 =
            let uu____9298 = un_uinst head1  in
            uu____9298.FStar_Syntax_Syntax.n  in
          (uu____9297, args)  in
        (match uu____9284 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9314) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____9334::(hd1,uu____9336)::(tl1,uu____9338)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____9385 =
               let uu____9390 =
                 let uu____9395 = list_elements tl1  in
                 FStar_Util.must uu____9395  in
               hd1 :: uu____9390  in
             FStar_Pervasives_Native.Some uu____9385
         | uu____9408 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____9426 .
    ('Auu____9426 -> 'Auu____9426) ->
      'Auu____9426 Prims.list -> 'Auu____9426 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____9449 = f a  in [uu____9449]
      | x::xs -> let uu____9454 = apply_last f xs  in x :: uu____9454
  
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
          let uu____9490 =
            let uu____9493 =
              let uu____9494 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____9494  in
            FStar_Syntax_Syntax.mk uu____9493  in
          uu____9490 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____9507 =
            let uu____9508 =
              let uu____9509 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____9509
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____9508 args  in
          uu____9507 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____9521 =
            let uu____9522 =
              let uu____9523 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____9523
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____9522 args  in
          uu____9521 FStar_Pervasives_Native.None pos  in
        let uu____9526 =
          let uu____9527 =
            let uu____9528 = FStar_Syntax_Syntax.iarg typ  in [uu____9528]
             in
          nil uu____9527 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____9534 =
                 let uu____9535 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____9536 =
                   let uu____9539 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____9540 =
                     let uu____9543 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____9543]  in
                   uu____9539 :: uu____9540  in
                 uu____9535 :: uu____9536  in
               cons1 uu____9534 t.FStar_Syntax_Syntax.pos) l uu____9526
  
let (uvar_from_id :
  Prims.int ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun id1  ->
    fun t  ->
      let uu____9552 =
        let uu____9555 =
          let uu____9556 =
            let uu____9573 = FStar_Syntax_Unionfind.from_id id1  in
            (uu____9573, t)  in
          FStar_Syntax_Syntax.Tm_uvar uu____9556  in
        FStar_Syntax_Syntax.mk uu____9555  in
      uu____9552 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        | uu____9633 -> false
  
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
          | uu____9730 -> false
  
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
        | uu____9868 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____9898 = FStar_ST.op_Bang debug_term_eq  in
          if uu____9898
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
        let t11 = let uu____10030 = unmeta_safe t1  in canon_app uu____10030
           in
        let t21 = let uu____10034 = unmeta_safe t2  in canon_app uu____10034
           in
        let uu____10035 =
          let uu____10040 =
            let uu____10041 =
              let uu____10044 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____10044  in
            uu____10041.FStar_Syntax_Syntax.n  in
          let uu____10045 =
            let uu____10046 =
              let uu____10049 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____10049  in
            uu____10046.FStar_Syntax_Syntax.n  in
          (uu____10040, uu____10045)  in
        match uu____10035 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____10050,uu____10051) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10058,FStar_Syntax_Syntax.Tm_uinst uu____10059) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____10066,uu____10067) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10092,FStar_Syntax_Syntax.Tm_delayed uu____10093) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____10118,uu____10119) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10146,FStar_Syntax_Syntax.Tm_ascribed uu____10147) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____10180 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____10180
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____10183 = FStar_Const.eq_const c1 c2  in
            check "const" uu____10183
        | (FStar_Syntax_Syntax.Tm_type
           uu____10184,FStar_Syntax_Syntax.Tm_type uu____10185) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____10234 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____10234) &&
              (let uu____10240 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____10240)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____10279 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____10279) &&
              (let uu____10285 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____10285)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____10299 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____10299)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____10346 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____10346) &&
              (let uu____10348 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____10348)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____10433 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____10433) &&
              (let uu____10435 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____10435)
        | (FStar_Syntax_Syntax.Tm_lazy uu____10450,uu____10451) ->
            let uu____10452 =
              let uu____10453 = unlazy t11  in
              term_eq_dbg dbg uu____10453 t21  in
            check "lazy_l" uu____10452
        | (uu____10454,FStar_Syntax_Syntax.Tm_lazy uu____10455) ->
            let uu____10456 =
              let uu____10457 = unlazy t21  in
              term_eq_dbg dbg t11 uu____10457  in
            check "lazy_r" uu____10456
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____10493 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____10493))
              &&
              (let uu____10495 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____10495)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____10497),FStar_Syntax_Syntax.Tm_uvar (u2,uu____10499)) ->
            check "uvar" (u1 = u2)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (check "meta_monadic lid" (FStar_Ident.lid_equals n1 n2)) &&
                   (let uu____10583 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____10583)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((check "meta_monadic_lift src"
                     (FStar_Ident.lid_equals s1 s2))
                    &&
                    (check "meta_monadic_lift tgt"
                       (FStar_Ident.lid_equals t13 t23)))
                   &&
                   (let uu____10599 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____10599)
             | (FStar_Syntax_Syntax.Meta_quoted
                (qt1,qi1),FStar_Syntax_Syntax.Meta_quoted (qt2,qi2)) ->
                 (check "meta_quoted dyn" (qi1 = qi2)) &&
                   (let uu____10613 = term_eq_dbg dbg qt1 qt2  in
                    check "meta_quoted payload" uu____10613)
             | uu____10614 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____10619) -> fail "unk"
        | (uu____10620,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____10621,uu____10622) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____10623,uu____10624) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____10625,uu____10626) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____10627,uu____10628) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____10629,uu____10630) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____10631,uu____10632) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____10649,uu____10650) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____10663,uu____10664) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____10671,uu____10672) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____10687,uu____10688) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____10711,uu____10712) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____10725,uu____10726) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____10743,uu____10744) ->
            fail "bottom"
        | (uu____10751,FStar_Syntax_Syntax.Tm_bvar uu____10752) ->
            fail "bottom"
        | (uu____10753,FStar_Syntax_Syntax.Tm_name uu____10754) ->
            fail "bottom"
        | (uu____10755,FStar_Syntax_Syntax.Tm_fvar uu____10756) ->
            fail "bottom"
        | (uu____10757,FStar_Syntax_Syntax.Tm_constant uu____10758) ->
            fail "bottom"
        | (uu____10759,FStar_Syntax_Syntax.Tm_type uu____10760) ->
            fail "bottom"
        | (uu____10761,FStar_Syntax_Syntax.Tm_abs uu____10762) ->
            fail "bottom"
        | (uu____10779,FStar_Syntax_Syntax.Tm_arrow uu____10780) ->
            fail "bottom"
        | (uu____10793,FStar_Syntax_Syntax.Tm_refine uu____10794) ->
            fail "bottom"
        | (uu____10801,FStar_Syntax_Syntax.Tm_app uu____10802) ->
            fail "bottom"
        | (uu____10817,FStar_Syntax_Syntax.Tm_match uu____10818) ->
            fail "bottom"
        | (uu____10841,FStar_Syntax_Syntax.Tm_let uu____10842) ->
            fail "bottom"
        | (uu____10855,FStar_Syntax_Syntax.Tm_uvar uu____10856) ->
            fail "bottom"
        | (uu____10873,FStar_Syntax_Syntax.Tm_meta uu____10874) ->
            fail "bottom"

and (arg_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun dbg  ->
    fun a1  ->
      fun a2  ->
        eqprod
          (fun t1  ->
             fun t2  ->
               let uu____10901 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____10901)
          (fun q1  -> fun q2  -> check "arg qual" (q1 = q2)) a1 a2

and (binder_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun dbg  ->
    fun b1  ->
      fun b2  ->
        eqprod
          (fun b11  ->
             fun b21  ->
               let uu____10922 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____10922)
          (fun q1  -> fun q2  -> check "binder qual" (q1 = q2)) b1 b2

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
        ((check "comp eff"
            (FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
               c21.FStar_Syntax_Syntax.effect_name))
           &&
           (let uu____10941 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____10941))
          && true

and (eq_flags_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.cflags -> FStar_Syntax_Syntax.cflags -> Prims.bool)
  = fun dbg  -> fun f1  -> fun f2  -> true

and (branch_eq_dbg :
  Prims.bool ->
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
  fun dbg  ->
    fun uu____10946  ->
      fun uu____10947  ->
        match (uu____10946, uu____10947) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____11072 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____11072) &&
               (let uu____11074 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____11074))
              &&
              (let uu____11076 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____11115 -> false  in
               check "branch when" uu____11076)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____11133 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____11133) &&
           (let uu____11139 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____11139))
          &&
          (let uu____11141 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____11141)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____11149 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____11149 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (bottom_fold :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f  in
      let tn =
        let uu____11204 = FStar_Syntax_Subst.compress t  in
        uu____11204.FStar_Syntax_Syntax.n  in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____11230 =
              let uu____11245 = ff f1  in
              let uu____11246 =
                FStar_List.map
                  (fun uu____11265  ->
                     match uu____11265 with
                     | (a,q) -> let uu____11276 = ff a  in (uu____11276, q))
                  args
                 in
              (uu____11245, uu____11246)  in
            FStar_Syntax_Syntax.Tm_app uu____11230
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____11306 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____11306 with
             | (bs1,t') ->
                 let t'' = ff t'  in
                 let uu____11314 =
                   let uu____11331 = FStar_Syntax_Subst.close bs1 t''  in
                   (bs1, uu____11331, k)  in
                 FStar_Syntax_Syntax.Tm_abs uu____11314)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____11358 = let uu____11365 = ff t1  in (uu____11365, us)
               in
            FStar_Syntax_Syntax.Tm_uinst uu____11358
        | uu____11366 -> tn  in
      f
        (let uu___58_11369 = t  in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.pos = (uu___58_11369.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___58_11369.FStar_Syntax_Syntax.vars)
         })
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11373 ->
        let uu____11398 =
          let uu____11399 = FStar_Syntax_Subst.compress t  in
          sizeof uu____11399  in
        (Prims.parse_int "1") + uu____11398
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____11401 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____11401
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____11403 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____11403
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____11410 = sizeof t1  in (FStar_List.length us) + uu____11410
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____11413) ->
        let uu____11434 = sizeof t1  in
        let uu____11435 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____11446  ->
                 match uu____11446 with
                 | (bv,uu____11452) ->
                     let uu____11453 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____11453) (Prims.parse_int "0") bs
           in
        uu____11434 + uu____11435
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____11476 = sizeof hd1  in
        let uu____11477 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____11488  ->
                 match uu____11488 with
                 | (arg,uu____11494) ->
                     let uu____11495 = sizeof arg  in acc + uu____11495)
            (Prims.parse_int "0") args
           in
        uu____11476 + uu____11477
    | uu____11496 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____11503 =
        let uu____11504 = un_uinst t  in uu____11504.FStar_Syntax_Syntax.n
         in
      match uu____11503 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____11508 -> false
  
let (is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  -> is_fvar FStar_Parser_Const.synth_lid t 
let (has_attribute :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Ident.lident -> Prims.bool)
  = fun attrs  -> fun attr  -> FStar_Util.for_some (is_fvar attr) attrs 
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> Prims.unit) =
  fun p  ->
    fun r  ->
      let set_options1 t s =
        let uu____11535 = FStar_Options.set_options t s  in
        match uu____11535 with
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
          ((let uu____11543 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____11543 FStar_Pervasives.ignore);
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
  