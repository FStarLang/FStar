open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____44879 = FStar_ST.op_Bang tts_f  in
    match uu____44879 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____44943 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____44943 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____44950 =
      let uu____44953 =
        let uu____44956 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____44956]  in
      FStar_List.append lid.FStar_Ident.ns uu____44953  in
    FStar_Ident.lid_of_ids uu____44950
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____44974 .
    (FStar_Syntax_Syntax.bv * 'Auu____44974) ->
      (FStar_Syntax_Syntax.term * 'Auu____44974)
  =
  fun uu____44987  ->
    match uu____44987 with
    | (b,imp) ->
        let uu____44994 = FStar_Syntax_Syntax.bv_to_name b  in
        (uu____44994, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____45046 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____45046
            then []
            else
              (let uu____45065 = arg_of_non_null_binder b  in [uu____45065])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____45100 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____45182 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45182
              then
                let b1 =
                  let uu____45208 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____45208, (FStar_Pervasives_Native.snd b))  in
                let uu____45215 = arg_of_non_null_binder b1  in
                (b1, uu____45215)
              else
                (let uu____45238 = arg_of_non_null_binder b  in
                 (b, uu____45238))))
       in
    FStar_All.pipe_right uu____45100 FStar_List.unzip
  
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
              let uu____45372 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45372
              then
                let uu____45381 = b  in
                match uu____45381 with
                | (a,imp) ->
                    let b1 =
                      let uu____45401 =
                        let uu____45403 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____45403  in
                      FStar_Ident.id_of_text uu____45401  in
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
        let uu____45448 =
          let uu____45455 =
            let uu____45456 =
              let uu____45471 = name_binders binders  in (uu____45471, comp)
               in
            FStar_Syntax_Syntax.Tm_arrow uu____45456  in
          FStar_Syntax_Syntax.mk uu____45455  in
        uu____45448 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____45493 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45530  ->
            match uu____45530 with
            | (t,imp) ->
                let uu____45541 =
                  let uu____45542 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____45542
                   in
                (uu____45541, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45597  ->
            match uu____45597 with
            | (t,imp) ->
                let uu____45614 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____45614, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____45627 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____45627
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____45639 . 'Auu____45639 -> 'Auu____45639 Prims.list =
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
          (fun uu____45765  ->
             fun uu____45766  ->
               match (uu____45765, uu____45766) with
               | ((x,uu____45792),(y,uu____45794)) ->
                   let uu____45815 =
                     let uu____45822 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____45822)  in
                   FStar_Syntax_Syntax.NT uu____45815) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____45838) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45844,uu____45845) ->
        unmeta e2
    | uu____45886 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____45900 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____45907 -> e1
         | uu____45916 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45918,uu____45919) ->
        unmeta_safe e2
    | uu____45960 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____45979 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____45982 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____45996 = univ_kernel u1  in
        (match uu____45996 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____46013 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____46022 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____46037 = univ_kernel u  in
    FStar_Pervasives_Native.snd uu____46037
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____46057,uu____46058) ->
          failwith "Impossible: compare_univs"
      | (uu____46062,FStar_Syntax_Syntax.U_bvar uu____46063) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____46068) ->
          ~- (Prims.parse_int "1")
      | (uu____46070,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____46073) -> ~- (Prims.parse_int "1")
      | (uu____46075,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____46079,FStar_Syntax_Syntax.U_unif
         uu____46080) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____46090,FStar_Syntax_Syntax.U_name
         uu____46091) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____46119 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____46121 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____46119 - uu____46121
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____46157 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____46157
                 (fun uu____46173  ->
                    match uu____46173 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____46201,uu____46202) ->
          ~- (Prims.parse_int "1")
      | (uu____46206,FStar_Syntax_Syntax.U_max uu____46207) ->
          (Prims.parse_int "1")
      | uu____46211 ->
          let uu____46216 = univ_kernel u1  in
          (match uu____46216 with
           | (k1,n1) ->
               let uu____46227 = univ_kernel u2  in
               (match uu____46227 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____46258 = compare_univs u1 u2  in
      uu____46258 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____46277 =
        let uu____46278 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____46278;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____46277
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____46298 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____46307 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____46330 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____46339 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____46366 =
          let uu____46367 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46367  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46366;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____46396 =
          let uu____46397 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46397  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46396;
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
      let uu___631_46433 = c  in
      let uu____46434 =
        let uu____46435 =
          let uu___633_46436 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___633_46436.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___633_46436.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___633_46436.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___633_46436.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____46435  in
      {
        FStar_Syntax_Syntax.n = uu____46434;
        FStar_Syntax_Syntax.pos = (uu___631_46433.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___631_46433.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____46462 -> c
        | FStar_Syntax_Syntax.GTotal uu____46471 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___645_46482 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___645_46482.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___645_46482.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___645_46482.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___645_46482.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___648_46483 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___648_46483.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___648_46483.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____46486  ->
           let uu____46487 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____46487)
  
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
    | uu____46527 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____46542 -> true
    | FStar_Syntax_Syntax.GTotal uu____46552 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___402_46577  ->
               match uu___402_46577 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46581 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___403_46594  ->
               match uu___403_46594 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46598 -> false)))
  
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
            (fun uu___404_46611  ->
               match uu___404_46611 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46615 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___405_46632  ->
            match uu___405_46632 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46636 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___406_46649  ->
            match uu___406_46649 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46653 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____46685 -> true
    | FStar_Syntax_Syntax.GTotal uu____46695 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___407_46710  ->
                   match uu___407_46710 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____46713 -> false)))
  
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
            (fun uu___408_46758  ->
               match uu___408_46758 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____46761 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46777 =
      let uu____46778 = FStar_Syntax_Subst.compress t  in
      uu____46778.FStar_Syntax_Syntax.n  in
    match uu____46777 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46782,c) -> is_pure_or_ghost_comp c
    | uu____46804 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____46819 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46828 =
      let uu____46829 = FStar_Syntax_Subst.compress t  in
      uu____46829.FStar_Syntax_Syntax.n  in
    match uu____46828 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46833,c) -> is_lemma_comp c
    | uu____46855 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____46863 =
      let uu____46864 = FStar_Syntax_Subst.compress t  in
      uu____46864.FStar_Syntax_Syntax.n  in
    match uu____46863 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____46868) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____46894) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____46931,t1,uu____46933) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____46959,uu____46960) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____47002) -> head_of t1
    | uu____47007 -> t
  
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
    | uu____47085 -> (t1, [])
  
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
        let uu____47167 = head_and_args' head1  in
        (match uu____47167 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____47236 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____47263) ->
        FStar_Syntax_Subst.compress t2
    | uu____47268 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____47276 =
      let uu____47277 = FStar_Syntax_Subst.compress t  in
      uu____47277.FStar_Syntax_Syntax.n  in
    match uu____47276 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____47281,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____47309)::uu____47310 ->
                  let pats' = unmeta pats  in
                  let uu____47370 = head_and_args pats'  in
                  (match uu____47370 with
                   | (head1,uu____47389) ->
                       let uu____47414 =
                         let uu____47415 = un_uinst head1  in
                         uu____47415.FStar_Syntax_Syntax.n  in
                       (match uu____47414 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____47420 -> false))
              | uu____47422 -> false)
         | uu____47434 -> false)
    | uu____47436 -> false
  
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
                (fun uu___409_47455  ->
                   match uu___409_47455 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____47458 -> false)))
    | uu____47460 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____47477) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____47487) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____47516 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____47525 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___827_47537 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___827_47537.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___827_47537.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___827_47537.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___827_47537.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____47551  ->
           let uu____47552 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____47552 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___410_47570  ->
            match uu___410_47570 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____47574 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____47582 -> []
    | FStar_Syntax_Syntax.GTotal uu____47599 -> []
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
    | uu____47643 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____47653,uu____47654) ->
        unascribe e2
    | uu____47695 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____47748,uu____47749) ->
          ascribe t' k
      | uu____47790 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____47817 =
      let uu____47826 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____47826  in
    uu____47817 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47882 =
      let uu____47883 = FStar_Syntax_Subst.compress t  in
      uu____47883.FStar_Syntax_Syntax.n  in
    match uu____47882 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____47887 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____47887
    | uu____47888 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47895 =
      let uu____47896 = FStar_Syntax_Subst.compress t  in
      uu____47896.FStar_Syntax_Syntax.n  in
    match uu____47895 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____47900 ->
             let uu____47909 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____47909
         | uu____47910 -> t)
    | uu____47911 -> t
  
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
      | uu____47935 -> false
  
let rec unlazy_as_t :
  'Auu____47948 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_Syntax_Syntax.term -> 'Auu____47948
  =
  fun k  ->
    fun t  ->
      let uu____47959 =
        let uu____47960 = FStar_Syntax_Subst.compress t  in
        uu____47960.FStar_Syntax_Syntax.n  in
      match uu____47959 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____47965;
            FStar_Syntax_Syntax.rng = uu____47966;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____47969 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____48010 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____48010;
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
    let uu____48023 =
      let uu____48038 = unascribe t  in head_and_args' uu____48038  in
    match uu____48023 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____48072 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____48083 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____48094 -> false
  
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
      | (NotEqual ,uu____48144) -> NotEqual
      | (uu____48145,NotEqual ) -> NotEqual
      | (Unknown ,uu____48146) -> Unknown
      | (uu____48147,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___411_48268 = if uu___411_48268 then Equal else Unknown
         in
      let equal_iff uu___412_48279 =
        if uu___412_48279 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____48300 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____48322 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____48322
        then
          let uu____48326 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____48403  ->
                    match uu____48403 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____48444 = eq_tm a1 a2  in
                        eq_inj acc uu____48444) Equal) uu____48326
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____48458 =
          let uu____48475 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____48475 head_and_args  in
        match uu____48458 with
        | (head1,args1) ->
            let uu____48528 =
              let uu____48545 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____48545 head_and_args  in
            (match uu____48528 with
             | (head2,args2) ->
                 let uu____48598 =
                   let uu____48603 =
                     let uu____48604 = un_uinst head1  in
                     uu____48604.FStar_Syntax_Syntax.n  in
                   let uu____48607 =
                     let uu____48608 = un_uinst head2  in
                     uu____48608.FStar_Syntax_Syntax.n  in
                   (uu____48603, uu____48607)  in
                 (match uu____48598 with
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
                  | uu____48635 -> FStar_Pervasives_Native.None))
         in
      let uu____48648 =
        let uu____48653 =
          let uu____48654 = unmeta t11  in uu____48654.FStar_Syntax_Syntax.n
           in
        let uu____48657 =
          let uu____48658 = unmeta t21  in uu____48658.FStar_Syntax_Syntax.n
           in
        (uu____48653, uu____48657)  in
      match uu____48648 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____48664,uu____48665) ->
          let uu____48666 = unlazy t11  in eq_tm uu____48666 t21
      | (uu____48667,FStar_Syntax_Syntax.Tm_lazy uu____48668) ->
          let uu____48669 = unlazy t21  in eq_tm t11 uu____48669
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____48672 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____48696 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____48696
            (fun uu____48744  ->
               match uu____48744 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____48759 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____48759
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____48773 = eq_tm f g  in
          eq_and uu____48773
            (fun uu____48776  ->
               let uu____48777 = eq_univs_list us vs  in equal_if uu____48777)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48779),uu____48780) -> Unknown
      | (uu____48781,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48782)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____48785 = FStar_Const.eq_const c d  in
          equal_iff uu____48785
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____48788)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____48790))) ->
          let uu____48819 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____48819
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____48873 =
            let uu____48878 =
              let uu____48879 = un_uinst h1  in
              uu____48879.FStar_Syntax_Syntax.n  in
            let uu____48882 =
              let uu____48883 = un_uinst h2  in
              uu____48883.FStar_Syntax_Syntax.n  in
            (uu____48878, uu____48882)  in
          (match uu____48873 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____48889 =
                    let uu____48891 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____48891  in
                  FStar_List.mem uu____48889 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____48893 ->
               let uu____48898 = eq_tm h1 h2  in
               eq_and uu____48898 (fun uu____48900  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____49006 = FStar_List.zip bs1 bs2  in
            let uu____49069 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____49106  ->
                 fun a  ->
                   match uu____49106 with
                   | (b1,b2) ->
                       eq_and a (fun uu____49199  -> branch_matches b1 b2))
              uu____49006 uu____49069
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____49204 = eq_univs u v1  in equal_if uu____49204
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____49218 = eq_quoteinfo q1 q2  in
          eq_and uu____49218 (fun uu____49220  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____49233 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____49233 (fun uu____49235  -> eq_tm phi1 phi2)
      | uu____49236 -> Unknown

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
      | ([],uu____49308) -> NotEqual
      | (uu____49339,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____49431 = eq_tm t1 t2  in
             match uu____49431 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____49432 = eq_antiquotes a11 a21  in
                 (match uu____49432 with
                  | NotEqual  -> NotEqual
                  | uu____49433 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____49448) -> NotEqual
      | (uu____49455,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____49485 -> NotEqual

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
        | (uu____49577,uu____49578) -> false  in
      let uu____49588 = b1  in
      match uu____49588 with
      | (p1,w1,t1) ->
          let uu____49622 = b2  in
          (match uu____49622 with
           | (p2,w2,t2) ->
               let uu____49656 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____49656
               then
                 let uu____49659 =
                   (let uu____49663 = eq_tm t1 t2  in uu____49663 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____49672 = eq_tm t11 t21  in
                             uu____49672 = Equal) w1 w2)
                    in
                 (if uu____49659 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____49737)::a11,(b,uu____49740)::b1) ->
          let uu____49814 = eq_tm a b  in
          (match uu____49814 with
           | Equal  -> eq_args a11 b1
           | uu____49815 -> Unknown)
      | uu____49816 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____49852) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____49858,uu____49859) ->
        unrefine t2
    | uu____49900 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____49908 =
      let uu____49909 = FStar_Syntax_Subst.compress t  in
      uu____49909.FStar_Syntax_Syntax.n  in
    match uu____49908 with
    | FStar_Syntax_Syntax.Tm_uvar uu____49913 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____49928) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____49933 ->
        let uu____49950 =
          let uu____49951 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____49951 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____49950 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____50014,uu____50015) ->
        is_uvar t1
    | uu____50056 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50065 =
      let uu____50066 = unrefine t  in uu____50066.FStar_Syntax_Syntax.n  in
    match uu____50065 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50072) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50098) -> is_unit t1
    | uu____50103 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50112 =
      let uu____50113 = FStar_Syntax_Subst.compress t  in
      uu____50113.FStar_Syntax_Syntax.n  in
    match uu____50112 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____50118 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50127 =
      let uu____50128 = unrefine t  in uu____50128.FStar_Syntax_Syntax.n  in
    match uu____50127 with
    | FStar_Syntax_Syntax.Tm_type uu____50132 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50136) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50162) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____50167,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____50189 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____50198 =
      let uu____50199 = FStar_Syntax_Subst.compress e  in
      uu____50199.FStar_Syntax_Syntax.n  in
    match uu____50198 with
    | FStar_Syntax_Syntax.Tm_abs uu____50203 -> true
    | uu____50223 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50232 =
      let uu____50233 = FStar_Syntax_Subst.compress t  in
      uu____50233.FStar_Syntax_Syntax.n  in
    match uu____50232 with
    | FStar_Syntax_Syntax.Tm_arrow uu____50237 -> true
    | uu____50253 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____50263) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____50269,uu____50270) ->
        pre_typ t2
    | uu____50311 -> t1
  
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
      let uu____50336 =
        let uu____50337 = un_uinst typ1  in uu____50337.FStar_Syntax_Syntax.n
         in
      match uu____50336 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____50402 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____50432 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____50453,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____50460) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____50465,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____50476,uu____50477,uu____50478,uu____50479,uu____50480) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____50490,uu____50491,uu____50492,uu____50493) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____50499,uu____50500,uu____50501,uu____50502,uu____50503) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____50511,uu____50512) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____50514,uu____50515) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____50518 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____50519 -> []
    | FStar_Syntax_Syntax.Sig_main uu____50520 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____50534 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___413_50560  ->
    match uu___413_50560 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____50574 'Auu____50575 .
    ('Auu____50574 FStar_Syntax_Syntax.syntax * 'Auu____50575) ->
      FStar_Range.range
  =
  fun uu____50586  ->
    match uu____50586 with | (hd1,uu____50594) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____50608 'Auu____50609 .
    ('Auu____50608 FStar_Syntax_Syntax.syntax * 'Auu____50609) Prims.list ->
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
      | uu____50707 ->
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
      let uu____50766 =
        FStar_List.map
          (fun uu____50793  ->
             match uu____50793 with
             | (bv,aq) ->
                 let uu____50812 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____50812, aq)) bs
         in
      mk_app f uu____50766
  
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
          let uu____50862 = FStar_Ident.range_of_lid l  in
          let uu____50863 =
            let uu____50872 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____50872  in
          uu____50863 FStar_Pervasives_Native.None uu____50862
      | uu____50880 ->
          let e =
            let uu____50894 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____50894 args  in
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
          let uu____50971 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____50971
          then
            let uu____50974 =
              let uu____50980 =
                let uu____50982 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____50982  in
              let uu____50985 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____50980, uu____50985)  in
            FStar_Ident.mk_ident uu____50974
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___1421_50990 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___1421_50990.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___1421_50990.FStar_Syntax_Syntax.sort)
          }  in
        let uu____50991 = mk_field_projector_name_from_ident lid nm  in
        (uu____50991, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____51003) -> ses
    | uu____51012 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____51023 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____51036 = FStar_Syntax_Unionfind.find uv  in
      match uu____51036 with
      | FStar_Pervasives_Native.Some uu____51039 ->
          let uu____51040 =
            let uu____51042 =
              let uu____51044 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____51044  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____51042  in
          failwith uu____51040
      | uu____51049 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____51132 -> q1 = q2
  
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
              let uu____51178 =
                let uu___1482_51179 = rc  in
                let uu____51180 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1482_51179.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____51180;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1482_51179.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____51178
           in
        match bs with
        | [] -> t
        | uu____51197 ->
            let body =
              let uu____51199 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____51199  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____51229 =
                   let uu____51236 =
                     let uu____51237 =
                       let uu____51256 =
                         let uu____51265 =
                           FStar_Syntax_Subst.close_binders bs  in
                         FStar_List.append uu____51265 bs'  in
                       let uu____51280 = close_lopt lopt'  in
                       (uu____51256, t1, uu____51280)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51237  in
                   FStar_Syntax_Syntax.mk uu____51236  in
                 uu____51229 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____51298 ->
                 let uu____51299 =
                   let uu____51306 =
                     let uu____51307 =
                       let uu____51326 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____51335 = close_lopt lopt  in
                       (uu____51326, body, uu____51335)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51307  in
                   FStar_Syntax_Syntax.mk uu____51306  in
                 uu____51299 FStar_Pervasives_Native.None
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
      | uu____51394 ->
          let uu____51403 =
            let uu____51410 =
              let uu____51411 =
                let uu____51426 = FStar_Syntax_Subst.close_binders bs  in
                let uu____51435 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____51426, uu____51435)  in
              FStar_Syntax_Syntax.Tm_arrow uu____51411  in
            FStar_Syntax_Syntax.mk uu____51410  in
          uu____51403 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____51487 =
        let uu____51488 = FStar_Syntax_Subst.compress t  in
        uu____51488.FStar_Syntax_Syntax.n  in
      match uu____51487 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____51518) ->
               let uu____51527 =
                 let uu____51528 = FStar_Syntax_Subst.compress tres  in
                 uu____51528.FStar_Syntax_Syntax.n  in
               (match uu____51527 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____51571 -> t)
           | uu____51572 -> t)
      | uu____51573 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____51591 =
        let uu____51592 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____51592 t.FStar_Syntax_Syntax.pos  in
      let uu____51593 =
        let uu____51600 =
          let uu____51601 =
            let uu____51608 =
              let uu____51611 =
                let uu____51612 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____51612]  in
              FStar_Syntax_Subst.close uu____51611 t  in
            (b, uu____51608)  in
          FStar_Syntax_Syntax.Tm_refine uu____51601  in
        FStar_Syntax_Syntax.mk uu____51600  in
      uu____51593 FStar_Pervasives_Native.None uu____51591
  
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
        let uu____51695 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____51695 with
         | (bs1,c1) ->
             let uu____51714 = is_total_comp c1  in
             if uu____51714
             then
               let uu____51729 = arrow_formals_comp (comp_result c1)  in
               (match uu____51729 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____51796;
           FStar_Syntax_Syntax.index = uu____51797;
           FStar_Syntax_Syntax.sort = s;_},uu____51799)
        ->
        let rec aux s1 k2 =
          let uu____51830 =
            let uu____51831 = FStar_Syntax_Subst.compress s1  in
            uu____51831.FStar_Syntax_Syntax.n  in
          match uu____51830 with
          | FStar_Syntax_Syntax.Tm_arrow uu____51846 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____51861;
                 FStar_Syntax_Syntax.index = uu____51862;
                 FStar_Syntax_Syntax.sort = s2;_},uu____51864)
              -> aux s2 k2
          | uu____51872 ->
              let uu____51873 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____51873)
           in
        aux s k1
    | uu____51888 ->
        let uu____51889 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____51889)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____51924 = arrow_formals_comp k  in
    match uu____51924 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____52066 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____52066 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____52090 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___414_52099  ->
                         match uu___414_52099 with
                         | FStar_Syntax_Syntax.DECREASES uu____52101 -> true
                         | uu____52105 -> false))
                  in
               (match uu____52090 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____52140 ->
                    let uu____52143 = is_total_comp c1  in
                    if uu____52143
                    then
                      let uu____52162 =
                        arrow_until_decreases (comp_result c1)  in
                      (match uu____52162 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____52255;
             FStar_Syntax_Syntax.index = uu____52256;
             FStar_Syntax_Syntax.sort = k2;_},uu____52258)
          -> arrow_until_decreases k2
      | uu____52266 -> ([], FStar_Pervasives_Native.None)  in
    let uu____52287 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____52287 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____52341 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____52362 =
                 FStar_Common.tabulate n_univs (fun uu____52372  -> false)
                  in
               let uu____52375 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____52400  ->
                         match uu____52400 with
                         | (x,uu____52409) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____52362 uu____52375)
           in
        ((n_univs + (FStar_List.length bs)), uu____52341)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____52471 =
            let uu___1604_52472 = rc  in
            let uu____52473 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1604_52472.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____52473;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1604_52472.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____52471
      | uu____52482 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____52516 =
        let uu____52517 =
          let uu____52520 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____52520  in
        uu____52517.FStar_Syntax_Syntax.n  in
      match uu____52516 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____52566 = aux t2 what  in
          (match uu____52566 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____52638 -> ([], t1, abs_body_lcomp)  in
    let uu____52655 = aux t FStar_Pervasives_Native.None  in
    match uu____52655 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____52703 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____52703 with
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
                    | (FStar_Pervasives_Native.None ,uu____52866) -> def
                    | (uu____52877,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____52889) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _52905  ->
                                  FStar_Syntax_Syntax.U_name _52905))
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
            let uu____52987 = FStar_Syntax_Subst.open_univ_vars_comp uvs c
               in
            (match uu____52987 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____53022 ->
            let t' = arrow binders c  in
            let uu____53034 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____53034 with
             | (uvs1,t'1) ->
                 let uu____53055 =
                   let uu____53056 = FStar_Syntax_Subst.compress t'1  in
                   uu____53056.FStar_Syntax_Syntax.n  in
                 (match uu____53055 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____53105 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____53130 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____53141 -> false
  
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
      let uu____53204 =
        let uu____53205 = pre_typ t  in uu____53205.FStar_Syntax_Syntax.n  in
      match uu____53204 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____53210 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____53224 =
        let uu____53225 = pre_typ t  in uu____53225.FStar_Syntax_Syntax.n  in
      match uu____53224 with
      | FStar_Syntax_Syntax.Tm_fvar uu____53229 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____53231) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____53257) ->
          is_constructed_typ t1 lid
      | uu____53262 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____53275 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____53276 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____53277 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____53279) -> get_tycon t2
    | uu____53304 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____53312 =
      let uu____53313 = un_uinst t  in uu____53313.FStar_Syntax_Syntax.n  in
    match uu____53312 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____53318 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____53332 =
        let uu____53336 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____53336  in
      match uu____53332 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____53368 -> false
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
  fun uu____53387  ->
    let u =
      let uu____53393 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _53410  -> FStar_Syntax_Syntax.U_unif _53410)
        uu____53393
       in
    let uu____53411 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____53411, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____53424 = eq_tm a a'  in
      match uu____53424 with | Equal  -> true | uu____53427 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____53432 =
    let uu____53439 =
      let uu____53440 =
        let uu____53441 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____53441
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____53440  in
    FStar_Syntax_Syntax.mk uu____53439  in
  uu____53432 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____53556 =
            let uu____53559 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____53560 =
              let uu____53567 =
                let uu____53568 =
                  let uu____53585 =
                    let uu____53596 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____53605 =
                      let uu____53616 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____53616]  in
                    uu____53596 :: uu____53605  in
                  (tand, uu____53585)  in
                FStar_Syntax_Syntax.Tm_app uu____53568  in
              FStar_Syntax_Syntax.mk uu____53567  in
            uu____53560 FStar_Pervasives_Native.None uu____53559  in
          FStar_Pervasives_Native.Some uu____53556
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____53696 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____53697 =
          let uu____53704 =
            let uu____53705 =
              let uu____53722 =
                let uu____53733 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____53742 =
                  let uu____53753 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____53753]  in
                uu____53733 :: uu____53742  in
              (op_t, uu____53722)  in
            FStar_Syntax_Syntax.Tm_app uu____53705  in
          FStar_Syntax_Syntax.mk uu____53704  in
        uu____53697 FStar_Pervasives_Native.None uu____53696
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____53813 =
      let uu____53820 =
        let uu____53821 =
          let uu____53838 =
            let uu____53849 = FStar_Syntax_Syntax.as_arg phi  in
            [uu____53849]  in
          (t_not, uu____53838)  in
        FStar_Syntax_Syntax.Tm_app uu____53821  in
      FStar_Syntax_Syntax.mk uu____53820  in
    uu____53813 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____54049 =
      let uu____54056 =
        let uu____54057 =
          let uu____54074 =
            let uu____54085 = FStar_Syntax_Syntax.as_arg e  in [uu____54085]
             in
          (b2t_v, uu____54074)  in
        FStar_Syntax_Syntax.Tm_app uu____54057  in
      FStar_Syntax_Syntax.mk uu____54056  in
    uu____54049 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____54132 =
      let uu____54133 = unmeta t  in uu____54133.FStar_Syntax_Syntax.n  in
    match uu____54132 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____54138 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54161 = is_t_true t1  in
      if uu____54161
      then t2
      else
        (let uu____54168 = is_t_true t2  in
         if uu____54168 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54196 = is_t_true t1  in
      if uu____54196
      then t_true
      else
        (let uu____54203 = is_t_true t2  in
         if uu____54203 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____54232 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____54233 =
        let uu____54240 =
          let uu____54241 =
            let uu____54258 =
              let uu____54269 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____54278 =
                let uu____54289 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____54289]  in
              uu____54269 :: uu____54278  in
            (teq, uu____54258)  in
          FStar_Syntax_Syntax.Tm_app uu____54241  in
        FStar_Syntax_Syntax.mk uu____54240  in
      uu____54233 FStar_Pervasives_Native.None uu____54232
  
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
          let uu____54359 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____54360 =
            let uu____54367 =
              let uu____54368 =
                let uu____54385 =
                  let uu____54396 = FStar_Syntax_Syntax.iarg t  in
                  let uu____54405 =
                    let uu____54416 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____54425 =
                      let uu____54436 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____54436]  in
                    uu____54416 :: uu____54425  in
                  uu____54396 :: uu____54405  in
                (eq_inst, uu____54385)  in
              FStar_Syntax_Syntax.Tm_app uu____54368  in
            FStar_Syntax_Syntax.mk uu____54367  in
          uu____54360 FStar_Pervasives_Native.None uu____54359
  
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
        let uu____54516 =
          let uu____54523 =
            let uu____54524 =
              let uu____54541 =
                let uu____54552 = FStar_Syntax_Syntax.iarg t  in
                let uu____54561 =
                  let uu____54572 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____54581 =
                    let uu____54592 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____54592]  in
                  uu____54572 :: uu____54581  in
                uu____54552 :: uu____54561  in
              (t_has_type1, uu____54541)  in
            FStar_Syntax_Syntax.Tm_app uu____54524  in
          FStar_Syntax_Syntax.mk uu____54523  in
        uu____54516 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____54672 =
          let uu____54679 =
            let uu____54680 =
              let uu____54697 =
                let uu____54708 = FStar_Syntax_Syntax.iarg t  in
                let uu____54717 =
                  let uu____54728 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____54728]  in
                uu____54708 :: uu____54717  in
              (t_with_type1, uu____54697)  in
            FStar_Syntax_Syntax.Tm_app uu____54680  in
          FStar_Syntax_Syntax.mk uu____54679  in
        uu____54672 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____54778 =
    let uu____54785 =
      let uu____54786 =
        let uu____54793 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____54793, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____54786  in
    FStar_Syntax_Syntax.mk uu____54785  in
  uu____54778 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____54811 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____54824 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____54835 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____54811 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____54856  -> c0)
  
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
        let uu____54939 =
          let uu____54946 =
            let uu____54947 =
              let uu____54964 =
                let uu____54975 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____54984 =
                  let uu____54995 =
                    let uu____55004 =
                      let uu____55005 =
                        let uu____55006 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____55006]  in
                      abs uu____55005 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____55004  in
                  [uu____54995]  in
                uu____54975 :: uu____54984  in
              (fa, uu____54964)  in
            FStar_Syntax_Syntax.Tm_app uu____54947  in
          FStar_Syntax_Syntax.mk uu____54946  in
        uu____54939 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____55136 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____55136
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____55155 -> true
    | uu____55157 -> false
  
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
          let uu____55204 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____55204, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____55233 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____55233, FStar_Pervasives_Native.None, t2)  in
        let uu____55247 =
          let uu____55248 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____55248  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____55247
  
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
      let uu____55324 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55327 =
        let uu____55338 = FStar_Syntax_Syntax.as_arg p  in [uu____55338]  in
      mk_app uu____55324 uu____55327
  
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
      let uu____55378 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55381 =
        let uu____55392 = FStar_Syntax_Syntax.as_arg p  in [uu____55392]  in
      mk_app uu____55378 uu____55381
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55427 = head_and_args t  in
    match uu____55427 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____55476 =
          let uu____55491 =
            let uu____55492 = FStar_Syntax_Subst.compress head3  in
            uu____55492.FStar_Syntax_Syntax.n  in
          (uu____55491, args)  in
        (match uu____55476 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____55511)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____55577 =
                    let uu____55582 =
                      let uu____55583 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____55583]  in
                    FStar_Syntax_Subst.open_term uu____55582 p  in
                  (match uu____55577 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____55640 -> failwith "impossible"  in
                       let uu____55648 =
                         let uu____55650 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____55650
                          in
                       if uu____55648
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____55666 -> FStar_Pervasives_Native.None)
         | uu____55669 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55700 = head_and_args t  in
    match uu____55700 with
    | (head1,args) ->
        let uu____55751 =
          let uu____55766 =
            let uu____55767 = FStar_Syntax_Subst.compress head1  in
            uu____55767.FStar_Syntax_Syntax.n  in
          (uu____55766, args)  in
        (match uu____55751 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____55789;
               FStar_Syntax_Syntax.vars = uu____55790;_},u::[]),(t1,uu____55793)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____55840 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55875 = head_and_args t  in
    match uu____55875 with
    | (head1,args) ->
        let uu____55926 =
          let uu____55941 =
            let uu____55942 = FStar_Syntax_Subst.compress head1  in
            uu____55942.FStar_Syntax_Syntax.n  in
          (uu____55941, args)  in
        (match uu____55926 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____55964;
               FStar_Syntax_Syntax.vars = uu____55965;_},u::[]),(t1,uu____55968)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____56015 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____56043 =
      let uu____56060 = unmeta t  in head_and_args uu____56060  in
    match uu____56043 with
    | (head1,uu____56063) ->
        let uu____56088 =
          let uu____56089 = un_uinst head1  in
          uu____56089.FStar_Syntax_Syntax.n  in
        (match uu____56088 with
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
         | uu____56094 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____56114 =
      let uu____56127 =
        let uu____56128 = FStar_Syntax_Subst.compress t  in
        uu____56128.FStar_Syntax_Syntax.n  in
      match uu____56127 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____56258 =
            let uu____56269 =
              let uu____56270 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____56270  in
            (b, uu____56269)  in
          FStar_Pervasives_Native.Some uu____56258
      | uu____56287 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____56114
      (fun uu____56325  ->
         match uu____56325 with
         | (b,c) ->
             let uu____56362 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____56362 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____56425 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____56462 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____56462
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____56514 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____56558 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____56600 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____56640) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____56652) ->
          unmeta_monadic t
      | uu____56665 -> f2  in
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
      let aux f2 uu____56761 =
        match uu____56761 with
        | (lid,arity) ->
            let uu____56770 =
              let uu____56787 = unmeta_monadic f2  in
              head_and_args uu____56787  in
            (match uu____56770 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____56817 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____56817
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____56897 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____56897)
      | uu____56910 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____56977 = head_and_args t1  in
        match uu____56977 with
        | (t2,args) ->
            let uu____57032 = un_uinst t2  in
            let uu____57033 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____57074  ->
                      match uu____57074 with
                      | (t3,imp) ->
                          let uu____57093 = unascribe t3  in
                          (uu____57093, imp)))
               in
            (uu____57032, uu____57033)
         in
      let rec aux qopt out t1 =
        let uu____57144 = let uu____57168 = flat t1  in (qopt, uu____57168)
           in
        match uu____57144 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57208;
                 FStar_Syntax_Syntax.vars = uu____57209;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____57212);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____57213;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____57214;_},uu____57215)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57317;
                 FStar_Syntax_Syntax.vars = uu____57318;_},uu____57319::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____57322);
                  FStar_Syntax_Syntax.pos = uu____57323;
                  FStar_Syntax_Syntax.vars = uu____57324;_},uu____57325)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57442;
               FStar_Syntax_Syntax.vars = uu____57443;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____57446);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____57447;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____57448;_},uu____57449)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57542 =
              let uu____57546 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57546  in
            aux uu____57542 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57556;
               FStar_Syntax_Syntax.vars = uu____57557;_},uu____57558::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____57561);
                FStar_Syntax_Syntax.pos = uu____57562;
                FStar_Syntax_Syntax.vars = uu____57563;_},uu____57564)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57673 =
              let uu____57677 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57677  in
            aux uu____57673 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____57687) ->
            let bs = FStar_List.rev out  in
            let uu____57740 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____57740 with
             | (bs1,t2) ->
                 let uu____57749 = patterns t2  in
                 (match uu____57749 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____57799 -> FStar_Pervasives_Native.None  in
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
      let uu____57891 = un_squash t  in
      FStar_Util.bind_opt uu____57891
        (fun t1  ->
           let uu____57907 = head_and_args' t1  in
           match uu____57907 with
           | (hd1,args) ->
               let uu____57946 =
                 let uu____57952 =
                   let uu____57953 = un_uinst hd1  in
                   uu____57953.FStar_Syntax_Syntax.n  in
                 (uu____57952, (FStar_List.length args))  in
               (match uu____57946 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57969) when
                    (_57969 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57972) when
                    (_57972 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57975) when
                    (_57975 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57978) when
                    (_57978 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57981) when
                    (_57981 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57984) when
                    (_57984 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57987) when
                    (_57987 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57990) when
                    (_57990 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____57991 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____58021 = un_squash t  in
      FStar_Util.bind_opt uu____58021
        (fun t1  ->
           let uu____58036 = arrow_one t1  in
           match uu____58036 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____58051 =
                 let uu____58053 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____58053  in
               if uu____58051
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____58063 = comp_to_comp_typ_nouniv c  in
                    uu____58063.FStar_Syntax_Syntax.result_typ  in
                  let uu____58064 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____58064
                  then
                    let uu____58071 = patterns q  in
                    match uu____58071 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____58134 =
                       let uu____58135 =
                         let uu____58140 =
                           let uu____58141 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____58152 =
                             let uu____58163 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____58163]  in
                           uu____58141 :: uu____58152  in
                         (FStar_Parser_Const.imp_lid, uu____58140)  in
                       BaseConn uu____58135  in
                     FStar_Pervasives_Native.Some uu____58134))
           | uu____58196 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____58204 = un_squash t  in
      FStar_Util.bind_opt uu____58204
        (fun t1  ->
           let uu____58235 = head_and_args' t1  in
           match uu____58235 with
           | (hd1,args) ->
               let uu____58274 =
                 let uu____58289 =
                   let uu____58290 = un_uinst hd1  in
                   uu____58290.FStar_Syntax_Syntax.n  in
                 (uu____58289, args)  in
               (match uu____58274 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____58307)::(a2,uu____58309)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____58360 =
                      let uu____58361 = FStar_Syntax_Subst.compress a2  in
                      uu____58361.FStar_Syntax_Syntax.n  in
                    (match uu____58360 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____58368) ->
                         let uu____58403 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____58403 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____58456 -> failwith "impossible"  in
                              let uu____58464 = patterns q1  in
                              (match uu____58464 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____58525 -> FStar_Pervasives_Native.None)
                | uu____58526 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____58549 = destruct_sq_forall phi  in
          (match uu____58549 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58559  -> FStar_Pervasives_Native.Some _58559)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58566 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____58572 = destruct_sq_exists phi  in
          (match uu____58572 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58582  -> FStar_Pervasives_Native.Some _58582)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58589 -> f1)
      | uu____58592 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____58596 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____58596
      (fun uu____58601  ->
         let uu____58602 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____58602
           (fun uu____58607  ->
              let uu____58608 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____58608
                (fun uu____58613  ->
                   let uu____58614 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____58614
                     (fun uu____58619  ->
                        let uu____58620 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____58620
                          (fun uu____58624  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____58637 =
      let uu____58638 = FStar_Syntax_Subst.compress t  in
      uu____58638.FStar_Syntax_Syntax.n  in
    match uu____58637 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____58645) ->
        let uu____58680 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____58680 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____58714 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____58714
             then
               let uu____58721 =
                 let uu____58732 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____58732]  in
               mk_app t uu____58721
             else e1)
    | uu____58759 ->
        let uu____58760 =
          let uu____58771 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____58771]  in
        mk_app t uu____58760
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____58813 =
            let uu____58818 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____58818  in
          let uu____58819 =
            let uu____58820 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____58820  in
          let uu____58823 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____58813 a.FStar_Syntax_Syntax.action_univs uu____58819
            FStar_Parser_Const.effect_Tot_lid uu____58823 [] pos
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
    let uu____58849 =
      let uu____58856 =
        let uu____58857 =
          let uu____58874 =
            let uu____58885 = FStar_Syntax_Syntax.as_arg t  in [uu____58885]
             in
          (reify_1, uu____58874)  in
        FStar_Syntax_Syntax.Tm_app uu____58857  in
      FStar_Syntax_Syntax.mk uu____58856  in
    uu____58849 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____58940 =
        let uu____58947 =
          let uu____58948 =
            let uu____58949 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____58949  in
          FStar_Syntax_Syntax.Tm_constant uu____58948  in
        FStar_Syntax_Syntax.mk uu____58947  in
      uu____58940 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____58954 =
      let uu____58961 =
        let uu____58962 =
          let uu____58979 =
            let uu____58990 = FStar_Syntax_Syntax.as_arg t  in [uu____58990]
             in
          (reflect_, uu____58979)  in
        FStar_Syntax_Syntax.Tm_app uu____58962  in
      FStar_Syntax_Syntax.mk uu____58961  in
    uu____58954 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____59037 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____59062 = unfold_lazy i  in delta_qualifier uu____59062
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____59064 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____59065 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____59066 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____59089 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____59102 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____59103 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____59110 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____59111 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____59127) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____59132;
           FStar_Syntax_Syntax.index = uu____59133;
           FStar_Syntax_Syntax.sort = t2;_},uu____59135)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____59144) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____59150,uu____59151) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____59193) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____59218,t2,uu____59220) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____59245,t2) -> delta_qualifier t2
  
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
    let uu____59284 = delta_qualifier t  in incr_delta_depth uu____59284
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____59292 =
      let uu____59293 = FStar_Syntax_Subst.compress t  in
      uu____59293.FStar_Syntax_Syntax.n  in
    match uu____59292 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____59298 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____59314 =
      let uu____59331 = unmeta e  in head_and_args uu____59331  in
    match uu____59314 with
    | (head1,args) ->
        let uu____59362 =
          let uu____59377 =
            let uu____59378 = un_uinst head1  in
            uu____59378.FStar_Syntax_Syntax.n  in
          (uu____59377, args)  in
        (match uu____59362 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____59396) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____59420::(hd1,uu____59422)::(tl1,uu____59424)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____59491 =
               let uu____59494 =
                 let uu____59497 = list_elements tl1  in
                 FStar_Util.must uu____59497  in
               hd1 :: uu____59494  in
             FStar_Pervasives_Native.Some uu____59491
         | uu____59506 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____59530 .
    ('Auu____59530 -> 'Auu____59530) ->
      'Auu____59530 Prims.list -> 'Auu____59530 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____59556 = f a  in [uu____59556]
      | x::xs -> let uu____59561 = apply_last f xs  in x :: uu____59561
  
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
          let uu____59616 =
            let uu____59623 =
              let uu____59624 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____59624  in
            FStar_Syntax_Syntax.mk uu____59623  in
          uu____59616 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____59641 =
            let uu____59646 =
              let uu____59647 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59647
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59646 args  in
          uu____59641 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____59663 =
            let uu____59668 =
              let uu____59669 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59669
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59668 args  in
          uu____59663 FStar_Pervasives_Native.None pos  in
        let uu____59672 =
          let uu____59673 =
            let uu____59674 = FStar_Syntax_Syntax.iarg typ  in [uu____59674]
             in
          nil uu____59673 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____59708 =
                 let uu____59709 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____59718 =
                   let uu____59729 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____59738 =
                     let uu____59749 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____59749]  in
                   uu____59729 :: uu____59738  in
                 uu____59709 :: uu____59718  in
               cons1 uu____59708 t.FStar_Syntax_Syntax.pos) l uu____59672
  
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
        | uu____59858 -> false
  
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
          | uu____59972 -> false
  
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
        | uu____60138 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____60187 = FStar_ST.op_Bang debug_term_eq  in
          if uu____60187
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
        let t11 = let uu____60409 = unmeta_safe t1  in canon_app uu____60409
           in
        let t21 = let uu____60415 = unmeta_safe t2  in canon_app uu____60415
           in
        let uu____60418 =
          let uu____60423 =
            let uu____60424 =
              let uu____60427 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____60427  in
            uu____60424.FStar_Syntax_Syntax.n  in
          let uu____60428 =
            let uu____60429 =
              let uu____60432 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____60432  in
            uu____60429.FStar_Syntax_Syntax.n  in
          (uu____60423, uu____60428)  in
        match uu____60418 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____60434,uu____60435) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60444,FStar_Syntax_Syntax.Tm_uinst uu____60445) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____60454,uu____60455) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60480,FStar_Syntax_Syntax.Tm_delayed uu____60481) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____60506,uu____60507) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60536,FStar_Syntax_Syntax.Tm_ascribed uu____60537) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____60576 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____60576
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____60581 = FStar_Const.eq_const c1 c2  in
            check "const" uu____60581
        | (FStar_Syntax_Syntax.Tm_type
           uu____60584,FStar_Syntax_Syntax.Tm_type uu____60585) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____60643 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____60643) &&
              (let uu____60653 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____60653)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____60702 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____60702) &&
              (let uu____60712 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____60712)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____60730 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____60730)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____60787 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____60787) &&
              (let uu____60791 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____60791)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____60880 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____60880) &&
              (let uu____60884 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____60884)
        | (FStar_Syntax_Syntax.Tm_lazy uu____60901,uu____60902) ->
            let uu____60903 =
              let uu____60905 = unlazy t11  in
              term_eq_dbg dbg uu____60905 t21  in
            check "lazy_l" uu____60903
        | (uu____60907,FStar_Syntax_Syntax.Tm_lazy uu____60908) ->
            let uu____60909 =
              let uu____60911 = unlazy t21  in
              term_eq_dbg dbg t11 uu____60911  in
            check "lazy_r" uu____60909
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____60956 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____60956))
              &&
              (let uu____60960 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____60960)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____60964),FStar_Syntax_Syntax.Tm_uvar (u2,uu____60966)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____61024 =
               let uu____61026 = eq_quoteinfo qi1 qi2  in uu____61026 = Equal
                in
             check "tm_quoted qi" uu____61024) &&
              (let uu____61029 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____61029)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____61059 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____61059) &&
                   (let uu____61063 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____61063)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____61082 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____61082) &&
                    (let uu____61086 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____61086))
                   &&
                   (let uu____61090 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____61090)
             | uu____61093 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____61099) -> fail "unk"
        | (uu____61101,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____61103,uu____61104) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____61106,uu____61107) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____61109,uu____61110) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____61112,uu____61113) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____61115,uu____61116) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____61118,uu____61119) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____61139,uu____61140) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____61156,uu____61157) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____61165,uu____61166) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____61184,uu____61185) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____61209,uu____61210) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____61225,uu____61226) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____61240,uu____61241) ->
            fail "bottom"
        | (uu____61249,FStar_Syntax_Syntax.Tm_bvar uu____61250) ->
            fail "bottom"
        | (uu____61252,FStar_Syntax_Syntax.Tm_name uu____61253) ->
            fail "bottom"
        | (uu____61255,FStar_Syntax_Syntax.Tm_fvar uu____61256) ->
            fail "bottom"
        | (uu____61258,FStar_Syntax_Syntax.Tm_constant uu____61259) ->
            fail "bottom"
        | (uu____61261,FStar_Syntax_Syntax.Tm_type uu____61262) ->
            fail "bottom"
        | (uu____61264,FStar_Syntax_Syntax.Tm_abs uu____61265) ->
            fail "bottom"
        | (uu____61285,FStar_Syntax_Syntax.Tm_arrow uu____61286) ->
            fail "bottom"
        | (uu____61302,FStar_Syntax_Syntax.Tm_refine uu____61303) ->
            fail "bottom"
        | (uu____61311,FStar_Syntax_Syntax.Tm_app uu____61312) ->
            fail "bottom"
        | (uu____61330,FStar_Syntax_Syntax.Tm_match uu____61331) ->
            fail "bottom"
        | (uu____61355,FStar_Syntax_Syntax.Tm_let uu____61356) ->
            fail "bottom"
        | (uu____61371,FStar_Syntax_Syntax.Tm_uvar uu____61372) ->
            fail "bottom"
        | (uu____61386,FStar_Syntax_Syntax.Tm_meta uu____61387) ->
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
               let uu____61422 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____61422)
          (fun q1  ->
             fun q2  ->
               let uu____61434 =
                 let uu____61436 = eq_aqual q1 q2  in uu____61436 = Equal  in
               check "arg qual" uu____61434) a1 a2

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
               let uu____61461 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____61461)
          (fun q1  ->
             fun q2  ->
               let uu____61473 =
                 let uu____61475 = eq_aqual q1 q2  in uu____61475 = Equal  in
               check "binder qual" uu____61473) b1 b2

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
        ((let uu____61495 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____61495) &&
           (let uu____61499 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____61499))
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
    fun uu____61509  ->
      fun uu____61510  ->
        match (uu____61509, uu____61510) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____61637 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____61637) &&
               (let uu____61641 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____61641))
              &&
              (let uu____61645 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____61687 -> false  in
               check "branch when" uu____61645)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____61708 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____61708) &&
           (let uu____61717 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____61717))
          &&
          (let uu____61721 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____61721)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____61738 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____61738 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____61792 ->
        let uu____61815 =
          let uu____61817 = FStar_Syntax_Subst.compress t  in
          sizeof uu____61817  in
        (Prims.parse_int "1") + uu____61815
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____61820 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61820
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____61824 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61824
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____61833 = sizeof t1  in (FStar_List.length us) + uu____61833
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____61837) ->
        let uu____61862 = sizeof t1  in
        let uu____61864 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____61879  ->
                 match uu____61879 with
                 | (bv,uu____61889) ->
                     let uu____61894 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____61894) (Prims.parse_int "0") bs
           in
        uu____61862 + uu____61864
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____61923 = sizeof hd1  in
        let uu____61925 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____61940  ->
                 match uu____61940 with
                 | (arg,uu____61950) ->
                     let uu____61955 = sizeof arg  in acc + uu____61955)
            (Prims.parse_int "0") args
           in
        uu____61923 + uu____61925
    | uu____61958 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____61972 =
        let uu____61973 = un_uinst t  in uu____61973.FStar_Syntax_Syntax.n
         in
      match uu____61972 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____61978 -> false
  
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
        let uu____62027 = FStar_Options.set_options t s  in
        match uu____62027 with
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
          ((let uu____62044 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____62044 (fun a1  -> ()));
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
          let uu____62059 = FStar_Options.internal_pop ()  in
          if uu____62059
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
    | FStar_Syntax_Syntax.Tm_delayed uu____62091 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____62118 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____62133 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____62134 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____62135 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____62144) ->
        let uu____62169 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____62169 with
         | (bs1,t2) ->
             let uu____62178 =
               FStar_List.collect
                 (fun uu____62190  ->
                    match uu____62190 with
                    | (b,uu____62200) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62205 = unbound_variables t2  in
             FStar_List.append uu____62178 uu____62205)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____62230 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____62230 with
         | (bs1,c1) ->
             let uu____62239 =
               FStar_List.collect
                 (fun uu____62251  ->
                    match uu____62251 with
                    | (b,uu____62261) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62266 = unbound_variables_comp c1  in
             FStar_List.append uu____62239 uu____62266)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____62275 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____62275 with
         | (bs,t2) ->
             let uu____62298 =
               FStar_List.collect
                 (fun uu____62310  ->
                    match uu____62310 with
                    | (b1,uu____62320) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____62325 = unbound_variables t2  in
             FStar_List.append uu____62298 uu____62325)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____62354 =
          FStar_List.collect
            (fun uu____62368  ->
               match uu____62368 with
               | (x,uu____62380) -> unbound_variables x) args
           in
        let uu____62389 = unbound_variables t1  in
        FStar_List.append uu____62354 uu____62389
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____62430 = unbound_variables t1  in
        let uu____62433 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____62448 = FStar_Syntax_Subst.open_branch br  in
                  match uu____62448 with
                  | (p,wopt,t2) ->
                      let uu____62470 = unbound_variables t2  in
                      let uu____62473 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____62470 uu____62473))
           in
        FStar_List.append uu____62430 uu____62433
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____62487) ->
        let uu____62528 = unbound_variables t1  in
        let uu____62531 =
          let uu____62534 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____62565 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____62534 uu____62565  in
        FStar_List.append uu____62528 uu____62531
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____62606 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____62609 =
          let uu____62612 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____62615 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____62620 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____62622 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____62622 with
                 | (uu____62643,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____62612 uu____62615  in
        FStar_List.append uu____62606 uu____62609
    | FStar_Syntax_Syntax.Tm_let ((uu____62645,lbs),t1) ->
        let uu____62665 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____62665 with
         | (lbs1,t2) ->
             let uu____62680 = unbound_variables t2  in
             let uu____62683 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____62690 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____62693 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____62690 uu____62693) lbs1
                in
             FStar_List.append uu____62680 uu____62683)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____62710 = unbound_variables t1  in
        let uu____62713 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____62752  ->
                      match uu____62752 with
                      | (a,uu____62764) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____62773,uu____62774,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____62780,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____62786 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____62795 -> []
          | FStar_Syntax_Syntax.Meta_named uu____62796 -> []  in
        FStar_List.append uu____62710 uu____62713

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____62803) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____62813) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____62823 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____62826 =
          FStar_List.collect
            (fun uu____62840  ->
               match uu____62840 with
               | (a,uu____62852) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____62823 uu____62826

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
            let uu____62967 = head_and_args h  in
            (match uu____62967 with
             | (head1,args) ->
                 let uu____63028 =
                   let uu____63029 = FStar_Syntax_Subst.compress head1  in
                   uu____63029.FStar_Syntax_Syntax.n  in
                 (match uu____63028 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____63082 -> aux (h :: acc) t))
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
      let uu____63106 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____63106 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2985_63148 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2985_63148.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2985_63148.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2985_63148.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2985_63148.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  