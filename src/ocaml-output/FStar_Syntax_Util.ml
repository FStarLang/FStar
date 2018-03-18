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
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___41_1299  ->
            match uu___41_1299 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1300 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___42_1307  ->
            match uu___42_1307 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1308 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____1326 -> true
    | FStar_Syntax_Syntax.GTotal uu____1335 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___43_1348  ->
                   match uu___43_1348 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1349 -> false)))
  
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
let (is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___44_1369  ->
               match uu___44_1369 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1370 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1377 =
      let uu____1378 = FStar_Syntax_Subst.compress t  in
      uu____1378.FStar_Syntax_Syntax.n  in
    match uu____1377 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1381,c) -> is_pure_or_ghost_comp c
    | uu____1399 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1408 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1412 =
      let uu____1413 = FStar_Syntax_Subst.compress t  in
      uu____1413.FStar_Syntax_Syntax.n  in
    match uu____1412 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1416,c) -> is_lemma_comp c
    | uu____1434 -> false
  
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
    | uu____1499 -> (t1, [])
  
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
        let uu____1564 = head_and_args' head1  in
        (match uu____1564 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1621 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1641) ->
        FStar_Syntax_Subst.compress t2
    | uu____1646 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1650 =
      let uu____1651 = FStar_Syntax_Subst.compress t  in
      uu____1651.FStar_Syntax_Syntax.n  in
    match uu____1650 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1654,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1676)::uu____1677 ->
                  let pats' = unmeta pats  in
                  let uu____1721 = head_and_args pats'  in
                  (match uu____1721 with
                   | (head1,uu____1737) ->
                       let uu____1758 =
                         let uu____1759 = un_uinst head1  in
                         uu____1759.FStar_Syntax_Syntax.n  in
                       (match uu____1758 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1763 -> false))
              | uu____1764 -> false)
         | uu____1773 -> false)
    | uu____1774 -> false
  
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
                (fun uu___45_1786  ->
                   match uu___45_1786 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1787 -> false)))
    | uu____1788 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1801) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1811) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____1831 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____1840 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___54_1852 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___54_1852.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___54_1852.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___54_1852.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___54_1852.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___46_1863  ->
            match uu___46_1863 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____1864 -> false))
  
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
    | uu____1880 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1886,uu____1887) ->
        unascribe e2
    | uu____1928 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1976,uu____1977) ->
          ascribe t' k
      | uu____2018 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2042 =
      let uu____2047 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2047  in
    uu____2042 i.FStar_Syntax_Syntax.kind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2092 =
      let uu____2093 = FStar_Syntax_Subst.compress t  in
      uu____2093.FStar_Syntax_Syntax.n  in
    match uu____2092 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2097 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2097
    | uu____2098 -> t
  
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
            let uu____2128 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2128;
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
    let uu____2134 =
      let uu____2147 = unascribe t  in head_and_args' uu____2147  in
    match uu____2134 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown [@@deriving show]
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2171 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2175 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2179 -> false
  
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
      let equal_if uu___47_2237 = if uu___47_2237 then Equal else Unknown  in
      let equal_iff uu___48_2242 = if uu___48_2242 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2256 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2264) -> NotEqual
        | (uu____2265,NotEqual ) -> NotEqual
        | (Unknown ,uu____2266) -> Unknown
        | (uu____2267,Unknown ) -> Unknown  in
      let notq t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (uu____2276,FStar_Syntax_Syntax.Meta_quoted uu____2277) -> false
        | uu____2288 -> true  in
      let equal_data f1 args1 f2 args2 =
        let uu____2326 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2326
        then
          let uu____2330 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2388  ->
                    match uu____2388 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2416 = eq_tm a1 a2  in
                        eq_inj acc uu____2416) Equal) uu____2330
        else NotEqual  in
      let uu____2418 =
        let uu____2423 =
          let uu____2424 = FStar_Syntax_Subst.compress t11  in
          uu____2424.FStar_Syntax_Syntax.n  in
        let uu____2427 =
          let uu____2428 = FStar_Syntax_Subst.compress t21  in
          uu____2428.FStar_Syntax_Syntax.n  in
        (uu____2423, uu____2427)  in
      match uu____2418 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2433,uu____2434) ->
          let uu____2435 = unlazy t11  in eq_tm uu____2435 t21
      | (uu____2436,FStar_Syntax_Syntax.Tm_lazy uu____2437) ->
          let uu____2438 = unlazy t21  in eq_tm t11 uu____2438
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
            (let uu____2456 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2456)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2469 = eq_tm f g  in
          eq_and uu____2469
            (fun uu____2472  ->
               let uu____2473 = eq_univs_list us vs  in equal_if uu____2473)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2474),uu____2475) -> Unknown
      | (uu____2476,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2477)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2480 = FStar_Const.eq_const c d  in equal_iff uu____2480
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2482),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2484)) ->
          let uu____2533 = FStar_Syntax_Unionfind.equiv u1 u2  in
          equal_if uu____2533
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2578 =
            let uu____2583 =
              let uu____2584 = un_uinst h1  in
              uu____2584.FStar_Syntax_Syntax.n  in
            let uu____2587 =
              let uu____2588 = un_uinst h2  in
              uu____2588.FStar_Syntax_Syntax.n  in
            (uu____2583, uu____2587)  in
          (match uu____2578 with
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
                 (let uu____2600 =
                    let uu____2601 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____2601  in
                  FStar_List.mem uu____2600 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____2602 ->
               let uu____2607 = eq_tm h1 h2  in
               eq_and uu____2607 (fun uu____2609  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____2714 = FStar_List.zip bs1 bs2  in
            let uu____2777 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____2814  ->
                 fun a  ->
                   match uu____2814 with
                   | (b1,b2) ->
                       eq_and a (fun uu____2907  -> branch_matches b1 b2))
              uu____2714 uu____2777
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____2911 = eq_univs u v1  in equal_if uu____2911
      | (FStar_Syntax_Syntax.Tm_meta (t1',uu____2913),uu____2914) when
          notq t11 -> eq_tm t1' t21
      | (uu____2919,FStar_Syntax_Syntax.Tm_meta (t2',uu____2921)) when
          notq t21 -> eq_tm t11 t2'
      | (FStar_Syntax_Syntax.Tm_meta
         (uu____2926,FStar_Syntax_Syntax.Meta_quoted (t12,uu____2928)),FStar_Syntax_Syntax.Tm_meta
         (uu____2929,FStar_Syntax_Syntax.Meta_quoted (t22,uu____2931))) ->
          eq_tm t12 t22
      | uu____2948 -> Unknown

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
        | (uu____3025,uu____3026) -> false  in
      let uu____3035 = b1  in
      match uu____3035 with
      | (p1,w1,t1) ->
          let uu____3069 = b2  in
          (match uu____3069 with
           | (p2,w2,t2) ->
               let uu____3103 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3103
               then
                 let uu____3104 =
                   (let uu____3107 = eq_tm t1 t2  in uu____3107 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3116 = eq_tm t11 t21  in
                             uu____3116 = Equal) w1 w2)
                    in
                 (if uu____3104 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3150)::a11,(b,uu____3153)::b1) ->
          let uu____3207 = eq_tm a b  in
          (match uu____3207 with
           | Equal  -> eq_args a11 b1
           | uu____3208 -> Unknown)
      | uu____3209 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3221) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3227,uu____3228) ->
        unrefine t2
    | uu____3269 -> t1
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3273 =
      let uu____3274 = unrefine t  in uu____3274.FStar_Syntax_Syntax.n  in
    match uu____3273 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3279) -> is_unit t1
    | uu____3284 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3288 =
      let uu____3289 = unrefine t  in uu____3289.FStar_Syntax_Syntax.n  in
    match uu____3288 with
    | FStar_Syntax_Syntax.Tm_type uu____3292 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3295) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3317) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3322,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3340 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____3344 =
      let uu____3345 = FStar_Syntax_Subst.compress e  in
      uu____3345.FStar_Syntax_Syntax.n  in
    match uu____3344 with
    | FStar_Syntax_Syntax.Tm_abs uu____3348 -> true
    | uu____3365 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3369 =
      let uu____3370 = FStar_Syntax_Subst.compress t  in
      uu____3370.FStar_Syntax_Syntax.n  in
    match uu____3369 with
    | FStar_Syntax_Syntax.Tm_arrow uu____3373 -> true
    | uu____3386 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3392) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3398,uu____3399) ->
        pre_typ t2
    | uu____3440 -> t1
  
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
      let uu____3458 =
        let uu____3459 = un_uinst typ1  in uu____3459.FStar_Syntax_Syntax.n
         in
      match uu____3458 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____3514 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____3538 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____3554,lids) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____3560,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3571,uu____3572,uu____3573,uu____3574,uu____3575) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____3585,uu____3586,uu____3587,uu____3588) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____3594,uu____3595,uu____3596,uu____3597,uu____3598) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3604,uu____3605) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3607,uu____3608) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3611 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____3612 -> []
    | FStar_Syntax_Syntax.Sig_main uu____3613 -> []
    | FStar_Syntax_Syntax.Sig_splice uu____3614 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____3625 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___49_3642  ->
    match uu___49_3642 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____3652 'Auu____3653 .
    ('Auu____3652 FStar_Syntax_Syntax.syntax,'Auu____3653)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____3663  ->
    match uu____3663 with | (hd1,uu____3671) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____3680 'Auu____3681 .
    ('Auu____3680 FStar_Syntax_Syntax.syntax,'Auu____3681)
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
          let uu____3801 =
            let uu____3804 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____3804  in
          uu____3801 FStar_Pervasives_Native.None
            (FStar_Ident.range_of_lid l)
      | uu____3808 ->
          let e =
            let uu____3820 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____3820 args  in
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
      let uu____3831 =
        let uu____3836 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____3836, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____3831
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
          let uu____3871 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____3871
          then
            let uu____3872 =
              let uu____3877 =
                let uu____3878 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____3878  in
              let uu____3879 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____3877, uu____3879)  in
            FStar_Ident.mk_ident uu____3872
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___55_3882 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___55_3882.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___55_3882.FStar_Syntax_Syntax.sort)
          }  in
        let uu____3883 = mk_field_projector_name_from_ident lid nm  in
        (uu____3883, y)
  
let (set_uvar :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit) =
  fun uv  ->
    fun t  ->
      let uu____3890 = FStar_Syntax_Unionfind.find uv  in
      match uu____3890 with
      | FStar_Pervasives_Native.Some uu____3893 ->
          let uu____3894 =
            let uu____3895 =
              let uu____3896 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____3896  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3895  in
          failwith uu____3894
      | uu____3897 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____3968 -> q1 = q2
  
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
              let uu____3999 =
                let uu___56_4000 = rc  in
                let uu____4001 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___56_4000.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____4001;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___56_4000.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____3999
           in
        match bs with
        | [] -> t
        | uu____4012 ->
            let body =
              let uu____4014 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4014  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4042 =
                   let uu____4045 =
                     let uu____4046 =
                       let uu____4063 =
                         let uu____4070 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4070 bs'  in
                       let uu____4081 = close_lopt lopt'  in
                       (uu____4063, t1, uu____4081)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4046  in
                   FStar_Syntax_Syntax.mk uu____4045  in
                 uu____4042 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4097 ->
                 let uu____4104 =
                   let uu____4107 =
                     let uu____4108 =
                       let uu____4125 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4126 = close_lopt lopt  in
                       (uu____4125, body, uu____4126)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4108  in
                   FStar_Syntax_Syntax.mk uu____4107  in
                 uu____4104 FStar_Pervasives_Native.None
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
      | uu____4164 ->
          let uu____4171 =
            let uu____4174 =
              let uu____4175 =
                let uu____4188 = FStar_Syntax_Subst.close_binders bs  in
                let uu____4189 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____4188, uu____4189)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4175  in
            FStar_Syntax_Syntax.mk uu____4174  in
          uu____4171 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____4220 =
        let uu____4221 = FStar_Syntax_Subst.compress t  in
        uu____4221.FStar_Syntax_Syntax.n  in
      match uu____4220 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____4247) ->
               let uu____4256 =
                 let uu____4257 = FStar_Syntax_Subst.compress tres  in
                 uu____4257.FStar_Syntax_Syntax.n  in
               (match uu____4256 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____4292 -> t)
           | uu____4293 -> t)
      | uu____4294 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____4303 =
        let uu____4304 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____4304 t.FStar_Syntax_Syntax.pos  in
      let uu____4305 =
        let uu____4308 =
          let uu____4309 =
            let uu____4316 =
              let uu____4317 =
                let uu____4318 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____4318]  in
              FStar_Syntax_Subst.close uu____4317 t  in
            (b, uu____4316)  in
          FStar_Syntax_Syntax.Tm_refine uu____4309  in
        FStar_Syntax_Syntax.mk uu____4308  in
      uu____4305 FStar_Pervasives_Native.None uu____4303
  
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
        let uu____4367 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____4367 with
         | (bs1,c1) ->
             let uu____4384 = is_tot_or_gtot_comp c1  in
             if uu____4384
             then
               let uu____4395 = arrow_formals_comp (comp_result c1)  in
               (match uu____4395 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____4441;
           FStar_Syntax_Syntax.index = uu____4442;
           FStar_Syntax_Syntax.sort = k2;_},uu____4444)
        -> arrow_formals_comp k2
    | uu____4451 ->
        let uu____4452 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4452)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____4478 = arrow_formals_comp k  in
    match uu____4478 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____4554 =
            let uu___57_4555 = rc  in
            let uu____4556 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___57_4555.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____4556;
              FStar_Syntax_Syntax.residual_flags =
                (uu___57_4555.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____4554
      | uu____4563 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____4591 =
        let uu____4592 =
          let uu____4595 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____4595  in
        uu____4592.FStar_Syntax_Syntax.n  in
      match uu____4591 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____4633 = aux t2 what  in
          (match uu____4633 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____4693 -> ([], t1, abs_body_lcomp)  in
    let uu____4706 = aux t FStar_Pervasives_Native.None  in
    match uu____4706 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____4748 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____4748 with
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
                    | (FStar_Pervasives_Native.None ,uu____4879) -> def
                    | (uu____4890,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____4902) ->
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
            let uu____5002 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____5002 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5031 ->
            let t' = arrow binders c  in
            let uu____5041 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5041 with
             | (uvs1,t'1) ->
                 let uu____5060 =
                   let uu____5061 = FStar_Syntax_Subst.compress t'1  in
                   uu____5061.FStar_Syntax_Syntax.n  in
                 (match uu____5060 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____5102 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____5119 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____5124 -> false
  
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
      let uu____5156 =
        let uu____5157 = pre_typ t  in uu____5157.FStar_Syntax_Syntax.n  in
      match uu____5156 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____5161 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____5168 =
        let uu____5169 = pre_typ t  in uu____5169.FStar_Syntax_Syntax.n  in
      match uu____5168 with
      | FStar_Syntax_Syntax.Tm_fvar uu____5172 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____5174) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5196) ->
          is_constructed_typ t1 lid
      | uu____5201 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____5210 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____5211 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____5212 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5214) -> get_tycon t2
    | uu____5235 -> FStar_Pervasives_Native.None
  
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
    let uu____5245 =
      let uu____5246 = un_uinst t  in uu____5246.FStar_Syntax_Syntax.n  in
    match uu____5245 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____5250 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____5257 =
        let uu____5260 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____5260  in
      match uu____5257 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____5273 -> false
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
  fun uu____5287  ->
    let u =
      let uu____5293 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_28  -> FStar_Syntax_Syntax.U_unif _0_28)
        uu____5293
       in
    let uu____5310 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____5310, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____5321 = eq_tm a a'  in
      match uu____5321 with | Equal  -> true | uu____5322 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____5325 =
    let uu____5328 =
      let uu____5329 =
        let uu____5330 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____5330
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____5329  in
    FStar_Syntax_Syntax.mk uu____5328  in
  uu____5325 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
  fvar_const FStar_Parser_Const.false_lid 
let (t_true : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.true_lid 
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
          let uu____5377 =
            let uu____5380 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____5381 =
              let uu____5384 =
                let uu____5385 =
                  let uu____5400 =
                    let uu____5403 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____5404 =
                      let uu____5407 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____5407]  in
                    uu____5403 :: uu____5404  in
                  (tand, uu____5400)  in
                FStar_Syntax_Syntax.Tm_app uu____5385  in
              FStar_Syntax_Syntax.mk uu____5384  in
            uu____5381 FStar_Pervasives_Native.None uu____5380  in
          FStar_Pervasives_Native.Some uu____5377
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____5430 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____5431 =
          let uu____5434 =
            let uu____5435 =
              let uu____5450 =
                let uu____5453 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____5454 =
                  let uu____5457 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____5457]  in
                uu____5453 :: uu____5454  in
              (op_t, uu____5450)  in
            FStar_Syntax_Syntax.Tm_app uu____5435  in
          FStar_Syntax_Syntax.mk uu____5434  in
        uu____5431 FStar_Pervasives_Native.None uu____5430
  
let (mk_neg :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____5470 =
      let uu____5473 =
        let uu____5474 =
          let uu____5489 =
            let uu____5492 = FStar_Syntax_Syntax.as_arg phi  in [uu____5492]
             in
          (t_not, uu____5489)  in
        FStar_Syntax_Syntax.Tm_app uu____5474  in
      FStar_Syntax_Syntax.mk uu____5473  in
    uu____5470 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____5553 =
      let uu____5556 =
        let uu____5557 =
          let uu____5572 =
            let uu____5575 = FStar_Syntax_Syntax.as_arg e  in [uu____5575]
             in
          (b2t_v, uu____5572)  in
        FStar_Syntax_Syntax.Tm_app uu____5557  in
      FStar_Syntax_Syntax.mk uu____5556  in
    uu____5553 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____5589 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____5590 =
        let uu____5593 =
          let uu____5594 =
            let uu____5609 =
              let uu____5612 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____5613 =
                let uu____5616 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____5616]  in
              uu____5612 :: uu____5613  in
            (teq, uu____5609)  in
          FStar_Syntax_Syntax.Tm_app uu____5594  in
        FStar_Syntax_Syntax.mk uu____5593  in
      uu____5590 FStar_Pervasives_Native.None uu____5589
  
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
          let uu____5635 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____5636 =
            let uu____5639 =
              let uu____5640 =
                let uu____5655 =
                  let uu____5658 = FStar_Syntax_Syntax.iarg t  in
                  let uu____5659 =
                    let uu____5662 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____5663 =
                      let uu____5666 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____5666]  in
                    uu____5662 :: uu____5663  in
                  uu____5658 :: uu____5659  in
                (eq_inst, uu____5655)  in
              FStar_Syntax_Syntax.Tm_app uu____5640  in
            FStar_Syntax_Syntax.mk uu____5639  in
          uu____5636 FStar_Pervasives_Native.None uu____5635
  
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
        let uu____5689 =
          let uu____5692 =
            let uu____5693 =
              let uu____5708 =
                let uu____5711 = FStar_Syntax_Syntax.iarg t  in
                let uu____5712 =
                  let uu____5715 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____5716 =
                    let uu____5719 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____5719]  in
                  uu____5715 :: uu____5716  in
                uu____5711 :: uu____5712  in
              (t_has_type1, uu____5708)  in
            FStar_Syntax_Syntax.Tm_app uu____5693  in
          FStar_Syntax_Syntax.mk uu____5692  in
        uu____5689 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____5744 =
          let uu____5747 =
            let uu____5748 =
              let uu____5763 =
                let uu____5766 = FStar_Syntax_Syntax.iarg t  in
                let uu____5767 =
                  let uu____5770 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____5770]  in
                uu____5766 :: uu____5767  in
              (t_with_type1, uu____5763)  in
            FStar_Syntax_Syntax.Tm_app uu____5748  in
          FStar_Syntax_Syntax.mk uu____5747  in
        uu____5744 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu____5780 =
    let uu____5783 =
      let uu____5784 =
        let uu____5791 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____5791, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____5784  in
    FStar_Syntax_Syntax.mk uu____5783  in
  uu____5780 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____5804 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____5817 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____5828 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____5804 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____5849  -> c0)
  
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
        let uu____5905 =
          let uu____5908 =
            let uu____5909 =
              let uu____5924 =
                let uu____5927 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____5928 =
                  let uu____5931 =
                    let uu____5932 =
                      let uu____5933 =
                        let uu____5934 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____5934]  in
                      abs uu____5933 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____5932  in
                  [uu____5931]  in
                uu____5927 :: uu____5928  in
              (fa, uu____5924)  in
            FStar_Syntax_Syntax.Tm_app uu____5909  in
          FStar_Syntax_Syntax.mk uu____5908  in
        uu____5905 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____5973 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____5973
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____5982 -> true
    | uu____5983 -> false
  
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
          let uu____6022 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____6022, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____6050 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____6050, FStar_Pervasives_Native.None, t2)  in
        let uu____6063 =
          let uu____6064 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____6064  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____6063
  
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
      let uu____6134 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6137 =
        let uu____6146 = FStar_Syntax_Syntax.as_arg p  in [uu____6146]  in
      mk_app uu____6134 uu____6137
  
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
      let uu____6156 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6159 =
        let uu____6168 = FStar_Syntax_Syntax.as_arg p  in [uu____6168]  in
      mk_app uu____6156 uu____6159
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6176 = head_and_args t  in
    match uu____6176 with
    | (head1,args) ->
        let uu____6217 =
          let uu____6230 =
            let uu____6231 = un_uinst head1  in
            uu____6231.FStar_Syntax_Syntax.n  in
          (uu____6230, args)  in
        (match uu____6217 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____6248)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____6300 =
                    let uu____6305 =
                      let uu____6306 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____6306]  in
                    FStar_Syntax_Subst.open_term uu____6305 p  in
                  (match uu____6300 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____6335 -> failwith "impossible"  in
                       let uu____6340 =
                         let uu____6341 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____6341
                          in
                       if uu____6340
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____6351 -> FStar_Pervasives_Native.None)
         | uu____6354 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6380 = head_and_args t  in
    match uu____6380 with
    | (head1,args) ->
        let uu____6425 =
          let uu____6438 =
            let uu____6439 = FStar_Syntax_Subst.compress head1  in
            uu____6439.FStar_Syntax_Syntax.n  in
          (uu____6438, args)  in
        (match uu____6425 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____6459;
               FStar_Syntax_Syntax.vars = uu____6460;_},u::[]),(t1,uu____6463)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____6502 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6532 = head_and_args t  in
    match uu____6532 with
    | (head1,args) ->
        let uu____6577 =
          let uu____6590 =
            let uu____6591 = FStar_Syntax_Subst.compress head1  in
            uu____6591.FStar_Syntax_Syntax.n  in
          (uu____6590, args)  in
        (match uu____6577 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____6611;
               FStar_Syntax_Syntax.vars = uu____6612;_},u::[]),(t1,uu____6615)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____6654 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____6676 = let uu____6691 = unmeta t  in head_and_args uu____6691
       in
    match uu____6676 with
    | (head1,uu____6693) ->
        let uu____6714 =
          let uu____6715 = un_uinst head1  in
          uu____6715.FStar_Syntax_Syntax.n  in
        (match uu____6714 with
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
         | uu____6719 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6735 =
      let uu____6748 =
        let uu____6749 = FStar_Syntax_Subst.compress t  in
        uu____6749.FStar_Syntax_Syntax.n  in
      match uu____6748 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____6858 =
            let uu____6867 =
              let uu____6868 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____6868  in
            (b, uu____6867)  in
          FStar_Pervasives_Native.Some uu____6858
      | uu____6881 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____6735
      (fun uu____6917  ->
         match uu____6917 with
         | (b,c) ->
             let uu____6952 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____6952 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____6999 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____7022 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____7022
  
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
    match projectee with | QAll _0 -> true | uu____7065 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____7101 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____7135 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____7168) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____7180) ->
          unmeta_monadic t
      | uu____7193 -> f2  in
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
      let aux f2 uu____7271 =
        match uu____7271 with
        | (lid,arity) ->
            let uu____7280 =
              let uu____7295 = unmeta_monadic f2  in head_and_args uu____7295
               in
            (match uu____7280 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____7321 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____7321
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____7396 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____7396)
      | uu____7407 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____7454 = head_and_args t1  in
        match uu____7454 with
        | (t2,args) ->
            let uu____7501 = un_uinst t2  in
            let uu____7502 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____7535  ->
                      match uu____7535 with
                      | (t3,imp) ->
                          let uu____7546 = unascribe t3  in (uu____7546, imp)))
               in
            (uu____7501, uu____7502)
         in
      let rec aux qopt out t1 =
        let uu____7581 = let uu____7598 = flat t1  in (qopt, uu____7598)  in
        match uu____7581 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____7625;
                 FStar_Syntax_Syntax.vars = uu____7626;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____7629);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____7630;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____7631;_},uu____7632)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____7709;
                 FStar_Syntax_Syntax.vars = uu____7710;_},uu____7711::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____7714);
                  FStar_Syntax_Syntax.pos = uu____7715;
                  FStar_Syntax_Syntax.vars = uu____7716;_},uu____7717)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7805;
               FStar_Syntax_Syntax.vars = uu____7806;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____7809);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7810;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7811;_},uu____7812)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7888;
               FStar_Syntax_Syntax.vars = uu____7889;_},uu____7890::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____7893);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____7894;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____7895;_},uu____7896)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____7984) ->
            let bs = FStar_List.rev out  in
            let uu____8018 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____8018 with
             | (bs1,t2) ->
                 let uu____8027 = patterns t2  in
                 (match uu____8027 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____8089 -> FStar_Pervasives_Native.None  in
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
      let uu____8155 = un_squash t  in
      FStar_Util.bind_opt uu____8155
        (fun t1  ->
           let uu____8171 = head_and_args' t1  in
           match uu____8171 with
           | (hd1,args) ->
               let uu____8204 =
                 let uu____8209 =
                   let uu____8210 = un_uinst hd1  in
                   uu____8210.FStar_Syntax_Syntax.n  in
                 (uu____8209, (FStar_List.length args))  in
               (match uu____8204 with
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
                | uu____8293 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____8316 = un_squash t  in
      FStar_Util.bind_opt uu____8316
        (fun t1  ->
           let uu____8331 = arrow_one t1  in
           match uu____8331 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____8346 =
                 let uu____8347 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____8347  in
               if uu____8346
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____8354 = comp_to_comp_typ_nouniv c  in
                    uu____8354.FStar_Syntax_Syntax.result_typ  in
                  let uu____8355 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____8355
                  then
                    let uu____8358 = patterns q  in
                    match uu____8358 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____8414 =
                       let uu____8415 =
                         let uu____8420 =
                           let uu____8423 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____8424 =
                             let uu____8427 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____8427]  in
                           uu____8423 :: uu____8424  in
                         (FStar_Parser_Const.imp_lid, uu____8420)  in
                       BaseConn uu____8415  in
                     FStar_Pervasives_Native.Some uu____8414))
           | uu____8430 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____8438 = un_squash t  in
      FStar_Util.bind_opt uu____8438
        (fun t1  ->
           let uu____8469 = head_and_args' t1  in
           match uu____8469 with
           | (hd1,args) ->
               let uu____8502 =
                 let uu____8515 =
                   let uu____8516 = un_uinst hd1  in
                   uu____8516.FStar_Syntax_Syntax.n  in
                 (uu____8515, args)  in
               (match uu____8502 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____8531)::(a2,uu____8533)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____8568 =
                      let uu____8569 = FStar_Syntax_Subst.compress a2  in
                      uu____8569.FStar_Syntax_Syntax.n  in
                    (match uu____8568 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____8576) ->
                         let uu____8603 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____8603 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____8642 -> failwith "impossible"  in
                              let uu____8647 = patterns q1  in
                              (match uu____8647 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____8714 -> FStar_Pervasives_Native.None)
                | uu____8715 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____8736 = destruct_sq_forall phi  in
          (match uu____8736 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8758 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____8764 = destruct_sq_exists phi  in
          (match uu____8764 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8786 -> f1)
      | uu____8789 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____8793 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____8793
      (fun uu____8798  ->
         let uu____8799 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____8799
           (fun uu____8804  ->
              let uu____8805 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____8805
                (fun uu____8810  ->
                   let uu____8811 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____8811
                     (fun uu____8816  ->
                        let uu____8817 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____8817
                          (fun uu____8821  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____8827 =
      let uu____8828 = FStar_Syntax_Subst.compress t  in
      uu____8828.FStar_Syntax_Syntax.n  in
    match uu____8827 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____8835) ->
        let uu____8862 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____8862 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____8888 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____8888
             then
               let uu____8891 =
                 let uu____8900 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____8900]  in
               mk_app t uu____8891
             else e1)
    | uu____8902 ->
        let uu____8903 =
          let uu____8912 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____8912]  in
        mk_app t uu____8903
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____8923 =
            let uu____8928 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.Delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____8928  in
          let uu____8929 =
            let uu____8930 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____8930  in
          let uu____8933 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____8923 a.FStar_Syntax_Syntax.action_univs uu____8929
            FStar_Parser_Const.effect_Tot_lid uu____8933 [] pos
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
    let uu____8960 =
      let uu____8963 =
        let uu____8964 =
          let uu____8979 =
            let uu____8982 = FStar_Syntax_Syntax.as_arg t  in [uu____8982]
             in
          (reify_, uu____8979)  in
        FStar_Syntax_Syntax.Tm_app uu____8964  in
      FStar_Syntax_Syntax.mk uu____8963  in
    uu____8960 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____8994 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____9020 = unfold_lazy i  in delta_qualifier uu____9020
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____9022 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____9023 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____9024 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____9047 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____9064 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____9065 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____9066 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____9080) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____9085;
           FStar_Syntax_Syntax.index = uu____9086;
           FStar_Syntax_Syntax.sort = t2;_},uu____9088)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____9096) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____9102,uu____9103) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____9145) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____9166,t2,uu____9168) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____9189,t2) -> delta_qualifier t2
  
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
    let uu____9215 = delta_qualifier t  in incr_delta_depth uu____9215
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9219 =
      let uu____9220 = FStar_Syntax_Subst.compress t  in
      uu____9220.FStar_Syntax_Syntax.n  in
    match uu____9219 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____9223 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9235 = let uu____9250 = unmeta e  in head_and_args uu____9250
       in
    match uu____9235 with
    | (head1,args) ->
        let uu____9277 =
          let uu____9290 =
            let uu____9291 = un_uinst head1  in
            uu____9291.FStar_Syntax_Syntax.n  in
          (uu____9290, args)  in
        (match uu____9277 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9307) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____9327::(hd1,uu____9329)::(tl1,uu____9331)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____9378 =
               let uu____9383 =
                 let uu____9388 = list_elements tl1  in
                 FStar_Util.must uu____9388  in
               hd1 :: uu____9383  in
             FStar_Pervasives_Native.Some uu____9378
         | uu____9401 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____9419 .
    ('Auu____9419 -> 'Auu____9419) ->
      'Auu____9419 Prims.list -> 'Auu____9419 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____9442 = f a  in [uu____9442]
      | x::xs -> let uu____9447 = apply_last f xs  in x :: uu____9447
  
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
          let uu____9483 =
            let uu____9486 =
              let uu____9487 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____9487  in
            FStar_Syntax_Syntax.mk uu____9486  in
          uu____9483 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____9500 =
            let uu____9501 =
              let uu____9502 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____9502
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____9501 args  in
          uu____9500 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____9514 =
            let uu____9515 =
              let uu____9516 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____9516
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____9515 args  in
          uu____9514 FStar_Pervasives_Native.None pos  in
        let uu____9519 =
          let uu____9520 =
            let uu____9521 = FStar_Syntax_Syntax.iarg typ  in [uu____9521]
             in
          nil uu____9520 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____9527 =
                 let uu____9528 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____9529 =
                   let uu____9532 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____9533 =
                     let uu____9536 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____9536]  in
                   uu____9532 :: uu____9533  in
                 uu____9528 :: uu____9529  in
               cons1 uu____9527 t.FStar_Syntax_Syntax.pos) l uu____9519
  
let (uvar_from_id :
  Prims.int ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun id1  ->
    fun t  ->
      let uu____9545 =
        let uu____9548 =
          let uu____9549 =
            let uu____9566 = FStar_Syntax_Unionfind.from_id id1  in
            (uu____9566, t)  in
          FStar_Syntax_Syntax.Tm_uvar uu____9549  in
        FStar_Syntax_Syntax.mk uu____9548  in
      uu____9545 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        | uu____9626 -> false
  
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
          | uu____9723 -> false
  
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
        | uu____9861 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____9891 = FStar_ST.op_Bang debug_term_eq  in
          if uu____9891
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
        let t11 = let uu____10023 = unmeta_safe t1  in canon_app uu____10023
           in
        let t21 = let uu____10027 = unmeta_safe t2  in canon_app uu____10027
           in
        let uu____10028 =
          let uu____10033 =
            let uu____10034 =
              let uu____10037 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____10037  in
            uu____10034.FStar_Syntax_Syntax.n  in
          let uu____10038 =
            let uu____10039 =
              let uu____10042 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____10042  in
            uu____10039.FStar_Syntax_Syntax.n  in
          (uu____10033, uu____10038)  in
        match uu____10028 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____10043,uu____10044) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10051,FStar_Syntax_Syntax.Tm_uinst uu____10052) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____10059,uu____10060) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10085,FStar_Syntax_Syntax.Tm_delayed uu____10086) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____10111,uu____10112) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10139,FStar_Syntax_Syntax.Tm_ascribed uu____10140) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____10173 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____10173
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____10176 = FStar_Const.eq_const c1 c2  in
            check "const" uu____10176
        | (FStar_Syntax_Syntax.Tm_type
           uu____10177,FStar_Syntax_Syntax.Tm_type uu____10178) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____10227 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____10227) &&
              (let uu____10233 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____10233)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____10272 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____10272) &&
              (let uu____10278 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____10278)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____10292 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____10292)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____10339 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____10339) &&
              (let uu____10341 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____10341)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____10426 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____10426) &&
              (let uu____10428 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____10428)
        | (FStar_Syntax_Syntax.Tm_lazy uu____10443,uu____10444) ->
            let uu____10445 =
              let uu____10446 = unlazy t11  in
              term_eq_dbg dbg uu____10446 t21  in
            check "lazy_l" uu____10445
        | (uu____10447,FStar_Syntax_Syntax.Tm_lazy uu____10448) ->
            let uu____10449 =
              let uu____10450 = unlazy t21  in
              term_eq_dbg dbg t11 uu____10450  in
            check "lazy_r" uu____10449
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____10486 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____10486))
              &&
              (let uu____10488 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____10488)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____10490),FStar_Syntax_Syntax.Tm_uvar (u2,uu____10492)) ->
            check "uvar" (u1 = u2)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (check "meta_monadic lid" (FStar_Ident.lid_equals n1 n2)) &&
                   (let uu____10576 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____10576)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((check "meta_monadic_lift src"
                     (FStar_Ident.lid_equals s1 s2))
                    &&
                    (check "meta_monadic_lift tgt"
                       (FStar_Ident.lid_equals t13 t23)))
                   &&
                   (let uu____10592 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____10592)
             | (FStar_Syntax_Syntax.Meta_quoted
                (qt1,qi1),FStar_Syntax_Syntax.Meta_quoted (qt2,qi2)) ->
                 (check "meta_quoted dyn" (qi1 = qi2)) &&
                   (let uu____10606 = term_eq_dbg dbg qt1 qt2  in
                    check "meta_quoted payload" uu____10606)
             | uu____10607 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____10612) -> fail "unk"
        | (uu____10613,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____10614,uu____10615) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____10616,uu____10617) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____10618,uu____10619) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____10620,uu____10621) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____10622,uu____10623) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____10624,uu____10625) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____10642,uu____10643) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____10656,uu____10657) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____10664,uu____10665) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____10680,uu____10681) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____10704,uu____10705) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____10718,uu____10719) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____10736,uu____10737) ->
            fail "bottom"
        | (uu____10744,FStar_Syntax_Syntax.Tm_bvar uu____10745) ->
            fail "bottom"
        | (uu____10746,FStar_Syntax_Syntax.Tm_name uu____10747) ->
            fail "bottom"
        | (uu____10748,FStar_Syntax_Syntax.Tm_fvar uu____10749) ->
            fail "bottom"
        | (uu____10750,FStar_Syntax_Syntax.Tm_constant uu____10751) ->
            fail "bottom"
        | (uu____10752,FStar_Syntax_Syntax.Tm_type uu____10753) ->
            fail "bottom"
        | (uu____10754,FStar_Syntax_Syntax.Tm_abs uu____10755) ->
            fail "bottom"
        | (uu____10772,FStar_Syntax_Syntax.Tm_arrow uu____10773) ->
            fail "bottom"
        | (uu____10786,FStar_Syntax_Syntax.Tm_refine uu____10787) ->
            fail "bottom"
        | (uu____10794,FStar_Syntax_Syntax.Tm_app uu____10795) ->
            fail "bottom"
        | (uu____10810,FStar_Syntax_Syntax.Tm_match uu____10811) ->
            fail "bottom"
        | (uu____10834,FStar_Syntax_Syntax.Tm_let uu____10835) ->
            fail "bottom"
        | (uu____10848,FStar_Syntax_Syntax.Tm_uvar uu____10849) ->
            fail "bottom"
        | (uu____10866,FStar_Syntax_Syntax.Tm_meta uu____10867) ->
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
               let uu____10894 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____10894)
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
               let uu____10915 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____10915)
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
           (let uu____10934 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____10934))
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
    fun uu____10939  ->
      fun uu____10940  ->
        match (uu____10939, uu____10940) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____11065 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____11065) &&
               (let uu____11067 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____11067))
              &&
              (let uu____11069 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____11108 -> false  in
               check "branch when" uu____11069)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____11126 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____11126) &&
           (let uu____11132 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____11132))
          &&
          (let uu____11134 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____11134)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____11142 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____11142 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (bottom_fold :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f  in
      let tn =
        let uu____11197 = FStar_Syntax_Subst.compress t  in
        uu____11197.FStar_Syntax_Syntax.n  in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____11223 =
              let uu____11238 = ff f1  in
              let uu____11239 =
                FStar_List.map
                  (fun uu____11258  ->
                     match uu____11258 with
                     | (a,q) -> let uu____11269 = ff a  in (uu____11269, q))
                  args
                 in
              (uu____11238, uu____11239)  in
            FStar_Syntax_Syntax.Tm_app uu____11223
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____11299 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____11299 with
             | (bs1,t') ->
                 let t'' = ff t'  in
                 let uu____11307 =
                   let uu____11324 = FStar_Syntax_Subst.close bs1 t''  in
                   (bs1, uu____11324, k)  in
                 FStar_Syntax_Syntax.Tm_abs uu____11307)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____11351 = let uu____11358 = ff t1  in (uu____11358, us)
               in
            FStar_Syntax_Syntax.Tm_uinst uu____11351
        | uu____11359 -> tn  in
      f
        (let uu___58_11362 = t  in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.pos = (uu___58_11362.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___58_11362.FStar_Syntax_Syntax.vars)
         })
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11366 ->
        let uu____11391 =
          let uu____11392 = FStar_Syntax_Subst.compress t  in
          sizeof uu____11392  in
        (Prims.parse_int "1") + uu____11391
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____11394 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____11394
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____11396 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____11396
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____11403 = sizeof t1  in (FStar_List.length us) + uu____11403
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____11406) ->
        let uu____11427 = sizeof t1  in
        let uu____11428 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____11439  ->
                 match uu____11439 with
                 | (bv,uu____11445) ->
                     let uu____11446 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____11446) (Prims.parse_int "0") bs
           in
        uu____11427 + uu____11428
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____11469 = sizeof hd1  in
        let uu____11470 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____11481  ->
                 match uu____11481 with
                 | (arg,uu____11487) ->
                     let uu____11488 = sizeof arg  in acc + uu____11488)
            (Prims.parse_int "0") args
           in
        uu____11469 + uu____11470
    | uu____11489 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____11496 =
        let uu____11497 = un_uinst t  in uu____11497.FStar_Syntax_Syntax.n
         in
      match uu____11496 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____11501 -> false
  
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
        let uu____11528 = FStar_Options.set_options t s  in
        match uu____11528 with
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
          ((let uu____11536 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____11536 FStar_Pervasives.ignore);
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
  