open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____44948 = FStar_ST.op_Bang tts_f  in
    match uu____44948 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____45012 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____45012 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____45019 =
      let uu____45022 =
        let uu____45025 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____45025]  in
      FStar_List.append lid.FStar_Ident.ns uu____45022  in
    FStar_Ident.lid_of_ids uu____45019
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____45043 .
    (FStar_Syntax_Syntax.bv * 'Auu____45043) ->
      (FStar_Syntax_Syntax.term * 'Auu____45043)
  =
  fun uu____45056  ->
    match uu____45056 with
    | (b,imp) ->
        let uu____45063 = FStar_Syntax_Syntax.bv_to_name b  in
        (uu____45063, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____45115 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____45115
            then []
            else
              (let uu____45134 = arg_of_non_null_binder b  in [uu____45134])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____45169 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____45251 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45251
              then
                let b1 =
                  let uu____45277 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____45277, (FStar_Pervasives_Native.snd b))  in
                let uu____45284 = arg_of_non_null_binder b1  in
                (b1, uu____45284)
              else
                (let uu____45307 = arg_of_non_null_binder b  in
                 (b, uu____45307))))
       in
    FStar_All.pipe_right uu____45169 FStar_List.unzip
  
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
              let uu____45441 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45441
              then
                let uu____45450 = b  in
                match uu____45450 with
                | (a,imp) ->
                    let b1 =
                      let uu____45470 =
                        let uu____45472 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____45472  in
                      FStar_Ident.id_of_text uu____45470  in
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
        let uu____45517 =
          let uu____45524 =
            let uu____45525 =
              let uu____45540 = name_binders binders  in (uu____45540, comp)
               in
            FStar_Syntax_Syntax.Tm_arrow uu____45525  in
          FStar_Syntax_Syntax.mk uu____45524  in
        uu____45517 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____45562 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45599  ->
            match uu____45599 with
            | (t,imp) ->
                let uu____45610 =
                  let uu____45611 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____45611
                   in
                (uu____45610, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45666  ->
            match uu____45666 with
            | (t,imp) ->
                let uu____45683 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____45683, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____45696 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____45696
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____45708 . 'Auu____45708 -> 'Auu____45708 Prims.list =
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
          (fun uu____45834  ->
             fun uu____45835  ->
               match (uu____45834, uu____45835) with
               | ((x,uu____45861),(y,uu____45863)) ->
                   let uu____45884 =
                     let uu____45891 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____45891)  in
                   FStar_Syntax_Syntax.NT uu____45884) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____45907) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45913,uu____45914) ->
        unmeta e2
    | uu____45955 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____45969 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____45976 -> e1
         | uu____45985 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45987,uu____45988) ->
        unmeta_safe e2
    | uu____46029 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____46048 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____46051 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____46065 = univ_kernel u1  in
        (match uu____46065 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____46082 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____46091 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____46106 = univ_kernel u  in
    FStar_Pervasives_Native.snd uu____46106
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____46126,uu____46127) ->
          failwith "Impossible: compare_univs"
      | (uu____46131,FStar_Syntax_Syntax.U_bvar uu____46132) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____46137) ->
          ~- (Prims.parse_int "1")
      | (uu____46139,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____46142) -> ~- (Prims.parse_int "1")
      | (uu____46144,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____46148,FStar_Syntax_Syntax.U_unif
         uu____46149) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____46159,FStar_Syntax_Syntax.U_name
         uu____46160) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____46188 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____46190 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____46188 - uu____46190
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____46226 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____46226
                 (fun uu____46242  ->
                    match uu____46242 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____46270,uu____46271) ->
          ~- (Prims.parse_int "1")
      | (uu____46275,FStar_Syntax_Syntax.U_max uu____46276) ->
          (Prims.parse_int "1")
      | uu____46280 ->
          let uu____46285 = univ_kernel u1  in
          (match uu____46285 with
           | (k1,n1) ->
               let uu____46296 = univ_kernel u2  in
               (match uu____46296 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____46327 = compare_univs u1 u2  in
      uu____46327 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____46346 =
        let uu____46347 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____46347;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____46346
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____46367 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____46376 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____46399 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____46408 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____46435 =
          let uu____46436 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46436  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46435;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____46465 =
          let uu____46466 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46466  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46465;
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
      let uu___631_46502 = c  in
      let uu____46503 =
        let uu____46504 =
          let uu___633_46505 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___633_46505.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___633_46505.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___633_46505.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___633_46505.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____46504  in
      {
        FStar_Syntax_Syntax.n = uu____46503;
        FStar_Syntax_Syntax.pos = (uu___631_46502.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___631_46502.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____46531 -> c
        | FStar_Syntax_Syntax.GTotal uu____46540 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___645_46551 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___645_46551.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___645_46551.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___645_46551.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___645_46551.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___648_46552 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___648_46552.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___648_46552.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____46555  ->
           let uu____46556 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____46556)
  
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
    | uu____46596 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____46611 -> true
    | FStar_Syntax_Syntax.GTotal uu____46621 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___402_46646  ->
               match uu___402_46646 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46650 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___403_46663  ->
               match uu___403_46663 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46667 -> false)))
  
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
            (fun uu___404_46680  ->
               match uu___404_46680 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46684 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___405_46701  ->
            match uu___405_46701 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46705 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___406_46718  ->
            match uu___406_46718 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46722 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____46754 -> true
    | FStar_Syntax_Syntax.GTotal uu____46764 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___407_46779  ->
                   match uu___407_46779 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____46782 -> false)))
  
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
            (fun uu___408_46827  ->
               match uu___408_46827 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____46830 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46846 =
      let uu____46847 = FStar_Syntax_Subst.compress t  in
      uu____46847.FStar_Syntax_Syntax.n  in
    match uu____46846 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46851,c) -> is_pure_or_ghost_comp c
    | uu____46873 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____46888 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46897 =
      let uu____46898 = FStar_Syntax_Subst.compress t  in
      uu____46898.FStar_Syntax_Syntax.n  in
    match uu____46897 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46902,c) -> is_lemma_comp c
    | uu____46924 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____46932 =
      let uu____46933 = FStar_Syntax_Subst.compress t  in
      uu____46933.FStar_Syntax_Syntax.n  in
    match uu____46932 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____46937) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____46963) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____47000,t1,uu____47002) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____47028,uu____47029) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____47071) -> head_of t1
    | uu____47076 -> t
  
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
    | uu____47154 -> (t1, [])
  
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
        let uu____47236 = head_and_args' head1  in
        (match uu____47236 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____47305 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____47332) ->
        FStar_Syntax_Subst.compress t2
    | uu____47337 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____47345 =
      let uu____47346 = FStar_Syntax_Subst.compress t  in
      uu____47346.FStar_Syntax_Syntax.n  in
    match uu____47345 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____47350,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____47378)::uu____47379 ->
                  let pats' = unmeta pats  in
                  let uu____47439 = head_and_args pats'  in
                  (match uu____47439 with
                   | (head1,uu____47458) ->
                       let uu____47483 =
                         let uu____47484 = un_uinst head1  in
                         uu____47484.FStar_Syntax_Syntax.n  in
                       (match uu____47483 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____47489 -> false))
              | uu____47491 -> false)
         | uu____47503 -> false)
    | uu____47505 -> false
  
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
                (fun uu___409_47524  ->
                   match uu___409_47524 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____47527 -> false)))
    | uu____47529 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____47546) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____47556) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____47585 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____47594 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___827_47606 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___827_47606.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___827_47606.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___827_47606.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___827_47606.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____47620  ->
           let uu____47621 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____47621 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___410_47639  ->
            match uu___410_47639 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____47643 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____47651 -> []
    | FStar_Syntax_Syntax.GTotal uu____47668 -> []
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
    | uu____47712 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____47722,uu____47723) ->
        unascribe e2
    | uu____47764 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____47817,uu____47818) ->
          ascribe t' k
      | uu____47859 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____47886 =
      let uu____47895 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____47895  in
    uu____47886 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47951 =
      let uu____47952 = FStar_Syntax_Subst.compress t  in
      uu____47952.FStar_Syntax_Syntax.n  in
    match uu____47951 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____47956 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____47956
    | uu____47957 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47964 =
      let uu____47965 = FStar_Syntax_Subst.compress t  in
      uu____47965.FStar_Syntax_Syntax.n  in
    match uu____47964 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____47969 ->
             let uu____47978 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____47978
         | uu____47979 -> t)
    | uu____47980 -> t
  
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
      | uu____48004 -> false
  
let rec unlazy_as_t :
  'Auu____48017 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_Syntax_Syntax.term -> 'Auu____48017
  =
  fun k  ->
    fun t  ->
      let uu____48028 =
        let uu____48029 = FStar_Syntax_Subst.compress t  in
        uu____48029.FStar_Syntax_Syntax.n  in
      match uu____48028 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____48034;
            FStar_Syntax_Syntax.rng = uu____48035;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____48038 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____48079 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____48079;
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
    let uu____48092 =
      let uu____48107 = unascribe t  in head_and_args' uu____48107  in
    match uu____48092 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____48141 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____48152 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____48163 -> false
  
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
      | (NotEqual ,uu____48213) -> NotEqual
      | (uu____48214,NotEqual ) -> NotEqual
      | (Unknown ,uu____48215) -> Unknown
      | (uu____48216,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___411_48337 = if uu___411_48337 then Equal else Unknown
         in
      let equal_iff uu___412_48348 =
        if uu___412_48348 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____48369 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____48391 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____48391
        then
          let uu____48395 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____48472  ->
                    match uu____48472 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____48513 = eq_tm a1 a2  in
                        eq_inj acc uu____48513) Equal) uu____48395
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____48527 =
          let uu____48544 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____48544 head_and_args  in
        match uu____48527 with
        | (head1,args1) ->
            let uu____48597 =
              let uu____48614 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____48614 head_and_args  in
            (match uu____48597 with
             | (head2,args2) ->
                 let uu____48667 =
                   let uu____48672 =
                     let uu____48673 = un_uinst head1  in
                     uu____48673.FStar_Syntax_Syntax.n  in
                   let uu____48676 =
                     let uu____48677 = un_uinst head2  in
                     uu____48677.FStar_Syntax_Syntax.n  in
                   (uu____48672, uu____48676)  in
                 (match uu____48667 with
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
                  | uu____48704 -> FStar_Pervasives_Native.None))
         in
      let uu____48717 =
        let uu____48722 =
          let uu____48723 = unmeta t11  in uu____48723.FStar_Syntax_Syntax.n
           in
        let uu____48726 =
          let uu____48727 = unmeta t21  in uu____48727.FStar_Syntax_Syntax.n
           in
        (uu____48722, uu____48726)  in
      match uu____48717 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____48733,uu____48734) ->
          let uu____48735 = unlazy t11  in eq_tm uu____48735 t21
      | (uu____48736,FStar_Syntax_Syntax.Tm_lazy uu____48737) ->
          let uu____48738 = unlazy t21  in eq_tm t11 uu____48738
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____48741 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____48765 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____48765
            (fun uu____48813  ->
               match uu____48813 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____48828 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____48828
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____48842 = eq_tm f g  in
          eq_and uu____48842
            (fun uu____48845  ->
               let uu____48846 = eq_univs_list us vs  in equal_if uu____48846)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48848),uu____48849) -> Unknown
      | (uu____48850,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48851)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____48854 = FStar_Const.eq_const c d  in
          equal_iff uu____48854
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____48857)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____48859))) ->
          let uu____48888 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____48888
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____48942 =
            let uu____48947 =
              let uu____48948 = un_uinst h1  in
              uu____48948.FStar_Syntax_Syntax.n  in
            let uu____48951 =
              let uu____48952 = un_uinst h2  in
              uu____48952.FStar_Syntax_Syntax.n  in
            (uu____48947, uu____48951)  in
          (match uu____48942 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____48958 =
                    let uu____48960 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____48960  in
                  FStar_List.mem uu____48958 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____48962 ->
               let uu____48967 = eq_tm h1 h2  in
               eq_and uu____48967 (fun uu____48969  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____49075 = FStar_List.zip bs1 bs2  in
            let uu____49138 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____49175  ->
                 fun a  ->
                   match uu____49175 with
                   | (b1,b2) ->
                       eq_and a (fun uu____49268  -> branch_matches b1 b2))
              uu____49075 uu____49138
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____49273 = eq_univs u v1  in equal_if uu____49273
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____49287 = eq_quoteinfo q1 q2  in
          eq_and uu____49287 (fun uu____49289  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____49302 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____49302 (fun uu____49304  -> eq_tm phi1 phi2)
      | uu____49305 -> Unknown

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
      | ([],uu____49377) -> NotEqual
      | (uu____49408,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____49500 = eq_tm t1 t2  in
             match uu____49500 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____49501 = eq_antiquotes a11 a21  in
                 (match uu____49501 with
                  | NotEqual  -> NotEqual
                  | uu____49502 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____49517) -> NotEqual
      | (uu____49524,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____49554 -> NotEqual

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
        | (uu____49646,uu____49647) -> false  in
      let uu____49657 = b1  in
      match uu____49657 with
      | (p1,w1,t1) ->
          let uu____49691 = b2  in
          (match uu____49691 with
           | (p2,w2,t2) ->
               let uu____49725 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____49725
               then
                 let uu____49728 =
                   (let uu____49732 = eq_tm t1 t2  in uu____49732 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____49741 = eq_tm t11 t21  in
                             uu____49741 = Equal) w1 w2)
                    in
                 (if uu____49728 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____49806)::a11,(b,uu____49809)::b1) ->
          let uu____49883 = eq_tm a b  in
          (match uu____49883 with
           | Equal  -> eq_args a11 b1
           | uu____49884 -> Unknown)
      | uu____49885 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____49921) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____49927,uu____49928) ->
        unrefine t2
    | uu____49969 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____49977 =
      let uu____49978 = FStar_Syntax_Subst.compress t  in
      uu____49978.FStar_Syntax_Syntax.n  in
    match uu____49977 with
    | FStar_Syntax_Syntax.Tm_uvar uu____49982 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____49997) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____50002 ->
        let uu____50019 =
          let uu____50020 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____50020 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____50019 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____50083,uu____50084) ->
        is_uvar t1
    | uu____50125 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50134 =
      let uu____50135 = unrefine t  in uu____50135.FStar_Syntax_Syntax.n  in
    match uu____50134 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50141) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50167) -> is_unit t1
    | uu____50172 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50181 =
      let uu____50182 = FStar_Syntax_Subst.compress t  in
      uu____50182.FStar_Syntax_Syntax.n  in
    match uu____50181 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____50187 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50196 =
      let uu____50197 = unrefine t  in uu____50197.FStar_Syntax_Syntax.n  in
    match uu____50196 with
    | FStar_Syntax_Syntax.Tm_type uu____50201 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50205) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50231) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____50236,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____50258 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____50267 =
      let uu____50268 = FStar_Syntax_Subst.compress e  in
      uu____50268.FStar_Syntax_Syntax.n  in
    match uu____50267 with
    | FStar_Syntax_Syntax.Tm_abs uu____50272 -> true
    | uu____50292 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50301 =
      let uu____50302 = FStar_Syntax_Subst.compress t  in
      uu____50302.FStar_Syntax_Syntax.n  in
    match uu____50301 with
    | FStar_Syntax_Syntax.Tm_arrow uu____50306 -> true
    | uu____50322 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____50332) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____50338,uu____50339) ->
        pre_typ t2
    | uu____50380 -> t1
  
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
      let uu____50405 =
        let uu____50406 = un_uinst typ1  in uu____50406.FStar_Syntax_Syntax.n
         in
      match uu____50405 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____50471 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____50501 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____50522,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____50529) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____50534,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____50545,uu____50546,uu____50547,uu____50548,uu____50549) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____50559,uu____50560,uu____50561,uu____50562) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____50568,uu____50569,uu____50570,uu____50571,uu____50572) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____50580,uu____50581) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____50583,uu____50584) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____50587 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____50588 -> []
    | FStar_Syntax_Syntax.Sig_main uu____50589 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____50603 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___413_50629  ->
    match uu___413_50629 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____50643 'Auu____50644 .
    ('Auu____50643 FStar_Syntax_Syntax.syntax * 'Auu____50644) ->
      FStar_Range.range
  =
  fun uu____50655  ->
    match uu____50655 with | (hd1,uu____50663) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____50677 'Auu____50678 .
    ('Auu____50677 FStar_Syntax_Syntax.syntax * 'Auu____50678) Prims.list ->
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
      | uu____50776 ->
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
      let uu____50835 =
        FStar_List.map
          (fun uu____50862  ->
             match uu____50862 with
             | (bv,aq) ->
                 let uu____50881 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____50881, aq)) bs
         in
      mk_app f uu____50835
  
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
          let uu____50931 = FStar_Ident.range_of_lid l  in
          let uu____50932 =
            let uu____50941 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____50941  in
          uu____50932 FStar_Pervasives_Native.None uu____50931
      | uu____50949 ->
          let e =
            let uu____50963 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____50963 args  in
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
          let uu____51040 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____51040
          then
            let uu____51043 =
              let uu____51049 =
                let uu____51051 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____51051  in
              let uu____51054 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____51049, uu____51054)  in
            FStar_Ident.mk_ident uu____51043
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___1421_51059 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___1421_51059.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___1421_51059.FStar_Syntax_Syntax.sort)
          }  in
        let uu____51060 = mk_field_projector_name_from_ident lid nm  in
        (uu____51060, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____51072) -> ses
    | uu____51081 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____51092 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____51105 = FStar_Syntax_Unionfind.find uv  in
      match uu____51105 with
      | FStar_Pervasives_Native.Some uu____51108 ->
          let uu____51109 =
            let uu____51111 =
              let uu____51113 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____51113  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____51111  in
          failwith uu____51109
      | uu____51118 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____51201 -> q1 = q2
  
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
              let uu____51247 =
                let uu___1482_51248 = rc  in
                let uu____51249 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1482_51248.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____51249;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1482_51248.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____51247
           in
        match bs with
        | [] -> t
        | uu____51266 ->
            let body =
              let uu____51268 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____51268  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____51298 =
                   let uu____51305 =
                     let uu____51306 =
                       let uu____51325 =
                         let uu____51334 =
                           FStar_Syntax_Subst.close_binders bs  in
                         FStar_List.append uu____51334 bs'  in
                       let uu____51349 = close_lopt lopt'  in
                       (uu____51325, t1, uu____51349)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51306  in
                   FStar_Syntax_Syntax.mk uu____51305  in
                 uu____51298 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____51367 ->
                 let uu____51368 =
                   let uu____51375 =
                     let uu____51376 =
                       let uu____51395 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____51404 = close_lopt lopt  in
                       (uu____51395, body, uu____51404)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51376  in
                   FStar_Syntax_Syntax.mk uu____51375  in
                 uu____51368 FStar_Pervasives_Native.None
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
      | uu____51463 ->
          let uu____51472 =
            let uu____51479 =
              let uu____51480 =
                let uu____51495 = FStar_Syntax_Subst.close_binders bs  in
                let uu____51504 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____51495, uu____51504)  in
              FStar_Syntax_Syntax.Tm_arrow uu____51480  in
            FStar_Syntax_Syntax.mk uu____51479  in
          uu____51472 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____51556 =
        let uu____51557 = FStar_Syntax_Subst.compress t  in
        uu____51557.FStar_Syntax_Syntax.n  in
      match uu____51556 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____51587) ->
               let uu____51596 =
                 let uu____51597 = FStar_Syntax_Subst.compress tres  in
                 uu____51597.FStar_Syntax_Syntax.n  in
               (match uu____51596 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____51640 -> t)
           | uu____51641 -> t)
      | uu____51642 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____51660 =
        let uu____51661 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____51661 t.FStar_Syntax_Syntax.pos  in
      let uu____51662 =
        let uu____51669 =
          let uu____51670 =
            let uu____51677 =
              let uu____51680 =
                let uu____51681 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____51681]  in
              FStar_Syntax_Subst.close uu____51680 t  in
            (b, uu____51677)  in
          FStar_Syntax_Syntax.Tm_refine uu____51670  in
        FStar_Syntax_Syntax.mk uu____51669  in
      uu____51662 FStar_Pervasives_Native.None uu____51660
  
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
        let uu____51764 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____51764 with
         | (bs1,c1) ->
             let uu____51783 = is_total_comp c1  in
             if uu____51783
             then
               let uu____51798 = arrow_formals_comp (comp_result c1)  in
               (match uu____51798 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____51865;
           FStar_Syntax_Syntax.index = uu____51866;
           FStar_Syntax_Syntax.sort = s;_},uu____51868)
        ->
        let rec aux s1 k2 =
          let uu____51899 =
            let uu____51900 = FStar_Syntax_Subst.compress s1  in
            uu____51900.FStar_Syntax_Syntax.n  in
          match uu____51899 with
          | FStar_Syntax_Syntax.Tm_arrow uu____51915 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____51930;
                 FStar_Syntax_Syntax.index = uu____51931;
                 FStar_Syntax_Syntax.sort = s2;_},uu____51933)
              -> aux s2 k2
          | uu____51941 ->
              let uu____51942 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____51942)
           in
        aux s k1
    | uu____51957 ->
        let uu____51958 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____51958)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____51993 = arrow_formals_comp k  in
    match uu____51993 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____52135 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____52135 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____52159 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___414_52168  ->
                         match uu___414_52168 with
                         | FStar_Syntax_Syntax.DECREASES uu____52170 -> true
                         | uu____52174 -> false))
                  in
               (match uu____52159 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____52209 ->
                    let uu____52212 = is_total_comp c1  in
                    if uu____52212
                    then
                      let uu____52231 =
                        arrow_until_decreases (comp_result c1)  in
                      (match uu____52231 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____52324;
             FStar_Syntax_Syntax.index = uu____52325;
             FStar_Syntax_Syntax.sort = k2;_},uu____52327)
          -> arrow_until_decreases k2
      | uu____52335 -> ([], FStar_Pervasives_Native.None)  in
    let uu____52356 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____52356 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____52410 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____52431 =
                 FStar_Common.tabulate n_univs (fun uu____52441  -> false)
                  in
               let uu____52444 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____52469  ->
                         match uu____52469 with
                         | (x,uu____52478) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____52431 uu____52444)
           in
        ((n_univs + (FStar_List.length bs)), uu____52410)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____52540 =
            let uu___1604_52541 = rc  in
            let uu____52542 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1604_52541.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____52542;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1604_52541.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____52540
      | uu____52551 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____52585 =
        let uu____52586 =
          let uu____52589 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____52589  in
        uu____52586.FStar_Syntax_Syntax.n  in
      match uu____52585 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____52635 = aux t2 what  in
          (match uu____52635 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____52707 -> ([], t1, abs_body_lcomp)  in
    let uu____52724 = aux t FStar_Pervasives_Native.None  in
    match uu____52724 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____52772 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____52772 with
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
                    | (FStar_Pervasives_Native.None ,uu____52935) -> def
                    | (uu____52946,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____52958) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _52974  ->
                                  FStar_Syntax_Syntax.U_name _52974))
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
            let uu____53056 = FStar_Syntax_Subst.open_univ_vars_comp uvs c
               in
            (match uu____53056 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____53091 ->
            let t' = arrow binders c  in
            let uu____53103 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____53103 with
             | (uvs1,t'1) ->
                 let uu____53124 =
                   let uu____53125 = FStar_Syntax_Subst.compress t'1  in
                   uu____53125.FStar_Syntax_Syntax.n  in
                 (match uu____53124 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____53174 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____53199 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____53210 -> false
  
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
      let uu____53273 =
        let uu____53274 = pre_typ t  in uu____53274.FStar_Syntax_Syntax.n  in
      match uu____53273 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____53279 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____53293 =
        let uu____53294 = pre_typ t  in uu____53294.FStar_Syntax_Syntax.n  in
      match uu____53293 with
      | FStar_Syntax_Syntax.Tm_fvar uu____53298 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____53300) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____53326) ->
          is_constructed_typ t1 lid
      | uu____53331 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____53344 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____53345 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____53346 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____53348) -> get_tycon t2
    | uu____53373 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____53381 =
      let uu____53382 = un_uinst t  in uu____53382.FStar_Syntax_Syntax.n  in
    match uu____53381 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____53387 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____53401 =
        let uu____53405 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____53405  in
      match uu____53401 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____53437 -> false
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
  fun uu____53456  ->
    let u =
      let uu____53462 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _53479  -> FStar_Syntax_Syntax.U_unif _53479)
        uu____53462
       in
    let uu____53480 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____53480, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____53493 = eq_tm a a'  in
      match uu____53493 with | Equal  -> true | uu____53496 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____53501 =
    let uu____53508 =
      let uu____53509 =
        let uu____53510 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____53510
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____53509  in
    FStar_Syntax_Syntax.mk uu____53508  in
  uu____53501 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____53625 =
            let uu____53628 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____53629 =
              let uu____53636 =
                let uu____53637 =
                  let uu____53654 =
                    let uu____53665 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____53674 =
                      let uu____53685 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____53685]  in
                    uu____53665 :: uu____53674  in
                  (tand, uu____53654)  in
                FStar_Syntax_Syntax.Tm_app uu____53637  in
              FStar_Syntax_Syntax.mk uu____53636  in
            uu____53629 FStar_Pervasives_Native.None uu____53628  in
          FStar_Pervasives_Native.Some uu____53625
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____53765 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____53766 =
          let uu____53773 =
            let uu____53774 =
              let uu____53791 =
                let uu____53802 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____53811 =
                  let uu____53822 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____53822]  in
                uu____53802 :: uu____53811  in
              (op_t, uu____53791)  in
            FStar_Syntax_Syntax.Tm_app uu____53774  in
          FStar_Syntax_Syntax.mk uu____53773  in
        uu____53766 FStar_Pervasives_Native.None uu____53765
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____53882 =
      let uu____53889 =
        let uu____53890 =
          let uu____53907 =
            let uu____53918 = FStar_Syntax_Syntax.as_arg phi  in
            [uu____53918]  in
          (t_not, uu____53907)  in
        FStar_Syntax_Syntax.Tm_app uu____53890  in
      FStar_Syntax_Syntax.mk uu____53889  in
    uu____53882 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____54118 =
      let uu____54125 =
        let uu____54126 =
          let uu____54143 =
            let uu____54154 = FStar_Syntax_Syntax.as_arg e  in [uu____54154]
             in
          (b2t_v, uu____54143)  in
        FStar_Syntax_Syntax.Tm_app uu____54126  in
      FStar_Syntax_Syntax.mk uu____54125  in
    uu____54118 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____54201 =
      let uu____54202 = unmeta t  in uu____54202.FStar_Syntax_Syntax.n  in
    match uu____54201 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____54207 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54230 = is_t_true t1  in
      if uu____54230
      then t2
      else
        (let uu____54237 = is_t_true t2  in
         if uu____54237 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54265 = is_t_true t1  in
      if uu____54265
      then t_true
      else
        (let uu____54272 = is_t_true t2  in
         if uu____54272 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____54301 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____54302 =
        let uu____54309 =
          let uu____54310 =
            let uu____54327 =
              let uu____54338 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____54347 =
                let uu____54358 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____54358]  in
              uu____54338 :: uu____54347  in
            (teq, uu____54327)  in
          FStar_Syntax_Syntax.Tm_app uu____54310  in
        FStar_Syntax_Syntax.mk uu____54309  in
      uu____54302 FStar_Pervasives_Native.None uu____54301
  
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
          let uu____54428 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____54429 =
            let uu____54436 =
              let uu____54437 =
                let uu____54454 =
                  let uu____54465 = FStar_Syntax_Syntax.iarg t  in
                  let uu____54474 =
                    let uu____54485 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____54494 =
                      let uu____54505 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____54505]  in
                    uu____54485 :: uu____54494  in
                  uu____54465 :: uu____54474  in
                (eq_inst, uu____54454)  in
              FStar_Syntax_Syntax.Tm_app uu____54437  in
            FStar_Syntax_Syntax.mk uu____54436  in
          uu____54429 FStar_Pervasives_Native.None uu____54428
  
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
        let uu____54585 =
          let uu____54592 =
            let uu____54593 =
              let uu____54610 =
                let uu____54621 = FStar_Syntax_Syntax.iarg t  in
                let uu____54630 =
                  let uu____54641 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____54650 =
                    let uu____54661 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____54661]  in
                  uu____54641 :: uu____54650  in
                uu____54621 :: uu____54630  in
              (t_has_type1, uu____54610)  in
            FStar_Syntax_Syntax.Tm_app uu____54593  in
          FStar_Syntax_Syntax.mk uu____54592  in
        uu____54585 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____54741 =
          let uu____54748 =
            let uu____54749 =
              let uu____54766 =
                let uu____54777 = FStar_Syntax_Syntax.iarg t  in
                let uu____54786 =
                  let uu____54797 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____54797]  in
                uu____54777 :: uu____54786  in
              (t_with_type1, uu____54766)  in
            FStar_Syntax_Syntax.Tm_app uu____54749  in
          FStar_Syntax_Syntax.mk uu____54748  in
        uu____54741 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____54847 =
    let uu____54854 =
      let uu____54855 =
        let uu____54862 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____54862, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____54855  in
    FStar_Syntax_Syntax.mk uu____54854  in
  uu____54847 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____54880 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____54893 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____54904 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____54880 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____54925  -> c0)
  
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
        let uu____55008 =
          let uu____55015 =
            let uu____55016 =
              let uu____55033 =
                let uu____55044 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____55053 =
                  let uu____55064 =
                    let uu____55073 =
                      let uu____55074 =
                        let uu____55075 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____55075]  in
                      abs uu____55074 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____55073  in
                  [uu____55064]  in
                uu____55044 :: uu____55053  in
              (fa, uu____55033)  in
            FStar_Syntax_Syntax.Tm_app uu____55016  in
          FStar_Syntax_Syntax.mk uu____55015  in
        uu____55008 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____55205 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____55205
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____55224 -> true
    | uu____55226 -> false
  
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
          let uu____55273 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____55273, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____55302 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____55302, FStar_Pervasives_Native.None, t2)  in
        let uu____55316 =
          let uu____55317 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____55317  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____55316
  
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
      let uu____55393 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55396 =
        let uu____55407 = FStar_Syntax_Syntax.as_arg p  in [uu____55407]  in
      mk_app uu____55393 uu____55396
  
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
      let uu____55447 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55450 =
        let uu____55461 = FStar_Syntax_Syntax.as_arg p  in [uu____55461]  in
      mk_app uu____55447 uu____55450
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55496 = head_and_args t  in
    match uu____55496 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____55545 =
          let uu____55560 =
            let uu____55561 = FStar_Syntax_Subst.compress head3  in
            uu____55561.FStar_Syntax_Syntax.n  in
          (uu____55560, args)  in
        (match uu____55545 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____55580)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____55646 =
                    let uu____55651 =
                      let uu____55652 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____55652]  in
                    FStar_Syntax_Subst.open_term uu____55651 p  in
                  (match uu____55646 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____55709 -> failwith "impossible"  in
                       let uu____55717 =
                         let uu____55719 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____55719
                          in
                       if uu____55717
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____55735 -> FStar_Pervasives_Native.None)
         | uu____55738 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55769 = head_and_args t  in
    match uu____55769 with
    | (head1,args) ->
        let uu____55820 =
          let uu____55835 =
            let uu____55836 = FStar_Syntax_Subst.compress head1  in
            uu____55836.FStar_Syntax_Syntax.n  in
          (uu____55835, args)  in
        (match uu____55820 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____55858;
               FStar_Syntax_Syntax.vars = uu____55859;_},u::[]),(t1,uu____55862)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____55909 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55944 = head_and_args t  in
    match uu____55944 with
    | (head1,args) ->
        let uu____55995 =
          let uu____56010 =
            let uu____56011 = FStar_Syntax_Subst.compress head1  in
            uu____56011.FStar_Syntax_Syntax.n  in
          (uu____56010, args)  in
        (match uu____55995 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____56033;
               FStar_Syntax_Syntax.vars = uu____56034;_},u::[]),(t1,uu____56037)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____56084 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____56112 =
      let uu____56129 = unmeta t  in head_and_args uu____56129  in
    match uu____56112 with
    | (head1,uu____56132) ->
        let uu____56157 =
          let uu____56158 = un_uinst head1  in
          uu____56158.FStar_Syntax_Syntax.n  in
        (match uu____56157 with
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
         | uu____56163 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____56183 =
      let uu____56196 =
        let uu____56197 = FStar_Syntax_Subst.compress t  in
        uu____56197.FStar_Syntax_Syntax.n  in
      match uu____56196 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____56327 =
            let uu____56338 =
              let uu____56339 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____56339  in
            (b, uu____56338)  in
          FStar_Pervasives_Native.Some uu____56327
      | uu____56356 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____56183
      (fun uu____56394  ->
         match uu____56394 with
         | (b,c) ->
             let uu____56431 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____56431 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____56494 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____56531 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____56531
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____56583 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____56627 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____56669 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____56709) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____56721) ->
          unmeta_monadic t
      | uu____56734 -> f2  in
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
      let aux f2 uu____56830 =
        match uu____56830 with
        | (lid,arity) ->
            let uu____56839 =
              let uu____56856 = unmeta_monadic f2  in
              head_and_args uu____56856  in
            (match uu____56839 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____56886 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____56886
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____56966 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____56966)
      | uu____56979 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____57046 = head_and_args t1  in
        match uu____57046 with
        | (t2,args) ->
            let uu____57101 = un_uinst t2  in
            let uu____57102 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____57143  ->
                      match uu____57143 with
                      | (t3,imp) ->
                          let uu____57162 = unascribe t3  in
                          (uu____57162, imp)))
               in
            (uu____57101, uu____57102)
         in
      let rec aux qopt out t1 =
        let uu____57213 = let uu____57237 = flat t1  in (qopt, uu____57237)
           in
        match uu____57213 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57277;
                 FStar_Syntax_Syntax.vars = uu____57278;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____57281);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____57282;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____57283;_},uu____57284)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57386;
                 FStar_Syntax_Syntax.vars = uu____57387;_},uu____57388::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____57391);
                  FStar_Syntax_Syntax.pos = uu____57392;
                  FStar_Syntax_Syntax.vars = uu____57393;_},uu____57394)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57511;
               FStar_Syntax_Syntax.vars = uu____57512;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____57515);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____57516;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____57517;_},uu____57518)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57611 =
              let uu____57615 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57615  in
            aux uu____57611 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57625;
               FStar_Syntax_Syntax.vars = uu____57626;_},uu____57627::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____57630);
                FStar_Syntax_Syntax.pos = uu____57631;
                FStar_Syntax_Syntax.vars = uu____57632;_},uu____57633)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57742 =
              let uu____57746 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57746  in
            aux uu____57742 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____57756) ->
            let bs = FStar_List.rev out  in
            let uu____57809 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____57809 with
             | (bs1,t2) ->
                 let uu____57818 = patterns t2  in
                 (match uu____57818 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____57868 -> FStar_Pervasives_Native.None  in
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
      let uu____57960 = un_squash t  in
      FStar_Util.bind_opt uu____57960
        (fun t1  ->
           let uu____57976 = head_and_args' t1  in
           match uu____57976 with
           | (hd1,args) ->
               let uu____58015 =
                 let uu____58021 =
                   let uu____58022 = un_uinst hd1  in
                   uu____58022.FStar_Syntax_Syntax.n  in
                 (uu____58021, (FStar_List.length args))  in
               (match uu____58015 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58038) when
                    (_58038 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58041) when
                    (_58041 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58044) when
                    (_58044 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58047) when
                    (_58047 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58050) when
                    (_58050 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58053) when
                    (_58053 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58056) when
                    (_58056 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58059) when
                    (_58059 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____58060 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____58090 = un_squash t  in
      FStar_Util.bind_opt uu____58090
        (fun t1  ->
           let uu____58105 = arrow_one t1  in
           match uu____58105 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____58120 =
                 let uu____58122 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____58122  in
               if uu____58120
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____58132 = comp_to_comp_typ_nouniv c  in
                    uu____58132.FStar_Syntax_Syntax.result_typ  in
                  let uu____58133 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____58133
                  then
                    let uu____58140 = patterns q  in
                    match uu____58140 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____58203 =
                       let uu____58204 =
                         let uu____58209 =
                           let uu____58210 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____58221 =
                             let uu____58232 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____58232]  in
                           uu____58210 :: uu____58221  in
                         (FStar_Parser_Const.imp_lid, uu____58209)  in
                       BaseConn uu____58204  in
                     FStar_Pervasives_Native.Some uu____58203))
           | uu____58265 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____58273 = un_squash t  in
      FStar_Util.bind_opt uu____58273
        (fun t1  ->
           let uu____58304 = head_and_args' t1  in
           match uu____58304 with
           | (hd1,args) ->
               let uu____58343 =
                 let uu____58358 =
                   let uu____58359 = un_uinst hd1  in
                   uu____58359.FStar_Syntax_Syntax.n  in
                 (uu____58358, args)  in
               (match uu____58343 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____58376)::(a2,uu____58378)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____58429 =
                      let uu____58430 = FStar_Syntax_Subst.compress a2  in
                      uu____58430.FStar_Syntax_Syntax.n  in
                    (match uu____58429 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____58437) ->
                         let uu____58472 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____58472 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____58525 -> failwith "impossible"  in
                              let uu____58533 = patterns q1  in
                              (match uu____58533 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____58594 -> FStar_Pervasives_Native.None)
                | uu____58595 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____58618 = destruct_sq_forall phi  in
          (match uu____58618 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58628  -> FStar_Pervasives_Native.Some _58628)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58635 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____58641 = destruct_sq_exists phi  in
          (match uu____58641 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58651  -> FStar_Pervasives_Native.Some _58651)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58658 -> f1)
      | uu____58661 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____58665 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____58665
      (fun uu____58670  ->
         let uu____58671 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____58671
           (fun uu____58676  ->
              let uu____58677 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____58677
                (fun uu____58682  ->
                   let uu____58683 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____58683
                     (fun uu____58688  ->
                        let uu____58689 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____58689
                          (fun uu____58693  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____58706 =
      let uu____58707 = FStar_Syntax_Subst.compress t  in
      uu____58707.FStar_Syntax_Syntax.n  in
    match uu____58706 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____58714) ->
        let uu____58749 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____58749 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____58783 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____58783
             then
               let uu____58790 =
                 let uu____58801 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____58801]  in
               mk_app t uu____58790
             else e1)
    | uu____58828 ->
        let uu____58829 =
          let uu____58840 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____58840]  in
        mk_app t uu____58829
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____58882 =
            let uu____58887 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____58887  in
          let uu____58888 =
            let uu____58889 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____58889  in
          let uu____58892 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____58882 a.FStar_Syntax_Syntax.action_univs uu____58888
            FStar_Parser_Const.effect_Tot_lid uu____58892 [] pos
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
    let uu____58918 =
      let uu____58925 =
        let uu____58926 =
          let uu____58943 =
            let uu____58954 = FStar_Syntax_Syntax.as_arg t  in [uu____58954]
             in
          (reify_1, uu____58943)  in
        FStar_Syntax_Syntax.Tm_app uu____58926  in
      FStar_Syntax_Syntax.mk uu____58925  in
    uu____58918 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____59009 =
        let uu____59016 =
          let uu____59017 =
            let uu____59018 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____59018  in
          FStar_Syntax_Syntax.Tm_constant uu____59017  in
        FStar_Syntax_Syntax.mk uu____59016  in
      uu____59009 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____59023 =
      let uu____59030 =
        let uu____59031 =
          let uu____59048 =
            let uu____59059 = FStar_Syntax_Syntax.as_arg t  in [uu____59059]
             in
          (reflect_, uu____59048)  in
        FStar_Syntax_Syntax.Tm_app uu____59031  in
      FStar_Syntax_Syntax.mk uu____59030  in
    uu____59023 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____59106 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____59131 = unfold_lazy i  in delta_qualifier uu____59131
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____59133 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____59134 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____59135 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____59158 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____59171 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____59172 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____59179 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____59180 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____59196) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____59201;
           FStar_Syntax_Syntax.index = uu____59202;
           FStar_Syntax_Syntax.sort = t2;_},uu____59204)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____59213) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____59219,uu____59220) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____59262) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____59287,t2,uu____59289) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____59314,t2) -> delta_qualifier t2
  
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
    let uu____59353 = delta_qualifier t  in incr_delta_depth uu____59353
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____59361 =
      let uu____59362 = FStar_Syntax_Subst.compress t  in
      uu____59362.FStar_Syntax_Syntax.n  in
    match uu____59361 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____59367 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____59383 =
      let uu____59400 = unmeta e  in head_and_args uu____59400  in
    match uu____59383 with
    | (head1,args) ->
        let uu____59431 =
          let uu____59446 =
            let uu____59447 = un_uinst head1  in
            uu____59447.FStar_Syntax_Syntax.n  in
          (uu____59446, args)  in
        (match uu____59431 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____59465) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____59489::(hd1,uu____59491)::(tl1,uu____59493)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____59560 =
               let uu____59563 =
                 let uu____59566 = list_elements tl1  in
                 FStar_Util.must uu____59566  in
               hd1 :: uu____59563  in
             FStar_Pervasives_Native.Some uu____59560
         | uu____59575 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____59599 .
    ('Auu____59599 -> 'Auu____59599) ->
      'Auu____59599 Prims.list -> 'Auu____59599 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____59625 = f a  in [uu____59625]
      | x::xs -> let uu____59630 = apply_last f xs  in x :: uu____59630
  
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
          let uu____59685 =
            let uu____59692 =
              let uu____59693 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____59693  in
            FStar_Syntax_Syntax.mk uu____59692  in
          uu____59685 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____59710 =
            let uu____59715 =
              let uu____59716 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59716
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59715 args  in
          uu____59710 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____59732 =
            let uu____59737 =
              let uu____59738 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59738
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59737 args  in
          uu____59732 FStar_Pervasives_Native.None pos  in
        let uu____59741 =
          let uu____59742 =
            let uu____59743 = FStar_Syntax_Syntax.iarg typ  in [uu____59743]
             in
          nil uu____59742 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____59777 =
                 let uu____59778 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____59787 =
                   let uu____59798 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____59807 =
                     let uu____59818 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____59818]  in
                   uu____59798 :: uu____59807  in
                 uu____59778 :: uu____59787  in
               cons1 uu____59777 t.FStar_Syntax_Syntax.pos) l uu____59741
  
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
        | uu____59927 -> false
  
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
          | uu____60041 -> false
  
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
        | uu____60207 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____60256 = FStar_ST.op_Bang debug_term_eq  in
          if uu____60256
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
        let t11 = let uu____60478 = unmeta_safe t1  in canon_app uu____60478
           in
        let t21 = let uu____60484 = unmeta_safe t2  in canon_app uu____60484
           in
        let uu____60487 =
          let uu____60492 =
            let uu____60493 =
              let uu____60496 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____60496  in
            uu____60493.FStar_Syntax_Syntax.n  in
          let uu____60497 =
            let uu____60498 =
              let uu____60501 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____60501  in
            uu____60498.FStar_Syntax_Syntax.n  in
          (uu____60492, uu____60497)  in
        match uu____60487 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____60503,uu____60504) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60513,FStar_Syntax_Syntax.Tm_uinst uu____60514) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____60523,uu____60524) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60549,FStar_Syntax_Syntax.Tm_delayed uu____60550) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____60575,uu____60576) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60605,FStar_Syntax_Syntax.Tm_ascribed uu____60606) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____60645 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____60645
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____60650 = FStar_Const.eq_const c1 c2  in
            check "const" uu____60650
        | (FStar_Syntax_Syntax.Tm_type
           uu____60653,FStar_Syntax_Syntax.Tm_type uu____60654) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____60712 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____60712) &&
              (let uu____60722 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____60722)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____60771 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____60771) &&
              (let uu____60781 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____60781)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____60799 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____60799)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____60856 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____60856) &&
              (let uu____60860 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____60860)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____60949 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____60949) &&
              (let uu____60953 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____60953)
        | (FStar_Syntax_Syntax.Tm_lazy uu____60970,uu____60971) ->
            let uu____60972 =
              let uu____60974 = unlazy t11  in
              term_eq_dbg dbg uu____60974 t21  in
            check "lazy_l" uu____60972
        | (uu____60976,FStar_Syntax_Syntax.Tm_lazy uu____60977) ->
            let uu____60978 =
              let uu____60980 = unlazy t21  in
              term_eq_dbg dbg t11 uu____60980  in
            check "lazy_r" uu____60978
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____61025 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____61025))
              &&
              (let uu____61029 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____61029)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____61033),FStar_Syntax_Syntax.Tm_uvar (u2,uu____61035)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____61093 =
               let uu____61095 = eq_quoteinfo qi1 qi2  in uu____61095 = Equal
                in
             check "tm_quoted qi" uu____61093) &&
              (let uu____61098 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____61098)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____61128 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____61128) &&
                   (let uu____61132 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____61132)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____61151 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____61151) &&
                    (let uu____61155 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____61155))
                   &&
                   (let uu____61159 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____61159)
             | uu____61162 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____61168) -> fail "unk"
        | (uu____61170,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____61172,uu____61173) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____61175,uu____61176) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____61178,uu____61179) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____61181,uu____61182) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____61184,uu____61185) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____61187,uu____61188) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____61208,uu____61209) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____61225,uu____61226) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____61234,uu____61235) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____61253,uu____61254) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____61278,uu____61279) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____61294,uu____61295) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____61309,uu____61310) ->
            fail "bottom"
        | (uu____61318,FStar_Syntax_Syntax.Tm_bvar uu____61319) ->
            fail "bottom"
        | (uu____61321,FStar_Syntax_Syntax.Tm_name uu____61322) ->
            fail "bottom"
        | (uu____61324,FStar_Syntax_Syntax.Tm_fvar uu____61325) ->
            fail "bottom"
        | (uu____61327,FStar_Syntax_Syntax.Tm_constant uu____61328) ->
            fail "bottom"
        | (uu____61330,FStar_Syntax_Syntax.Tm_type uu____61331) ->
            fail "bottom"
        | (uu____61333,FStar_Syntax_Syntax.Tm_abs uu____61334) ->
            fail "bottom"
        | (uu____61354,FStar_Syntax_Syntax.Tm_arrow uu____61355) ->
            fail "bottom"
        | (uu____61371,FStar_Syntax_Syntax.Tm_refine uu____61372) ->
            fail "bottom"
        | (uu____61380,FStar_Syntax_Syntax.Tm_app uu____61381) ->
            fail "bottom"
        | (uu____61399,FStar_Syntax_Syntax.Tm_match uu____61400) ->
            fail "bottom"
        | (uu____61424,FStar_Syntax_Syntax.Tm_let uu____61425) ->
            fail "bottom"
        | (uu____61440,FStar_Syntax_Syntax.Tm_uvar uu____61441) ->
            fail "bottom"
        | (uu____61455,FStar_Syntax_Syntax.Tm_meta uu____61456) ->
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
               let uu____61491 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____61491)
          (fun q1  ->
             fun q2  ->
               let uu____61503 =
                 let uu____61505 = eq_aqual q1 q2  in uu____61505 = Equal  in
               check "arg qual" uu____61503) a1 a2

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
               let uu____61530 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____61530)
          (fun q1  ->
             fun q2  ->
               let uu____61542 =
                 let uu____61544 = eq_aqual q1 q2  in uu____61544 = Equal  in
               check "binder qual" uu____61542) b1 b2

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
        ((let uu____61564 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____61564) &&
           (let uu____61568 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____61568))
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
    fun uu____61578  ->
      fun uu____61579  ->
        match (uu____61578, uu____61579) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____61706 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____61706) &&
               (let uu____61710 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____61710))
              &&
              (let uu____61714 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____61756 -> false  in
               check "branch when" uu____61714)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____61777 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____61777) &&
           (let uu____61786 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____61786))
          &&
          (let uu____61790 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____61790)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____61807 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____61807 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____61861 ->
        let uu____61884 =
          let uu____61886 = FStar_Syntax_Subst.compress t  in
          sizeof uu____61886  in
        (Prims.parse_int "1") + uu____61884
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____61889 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61889
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____61893 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61893
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____61902 = sizeof t1  in (FStar_List.length us) + uu____61902
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____61906) ->
        let uu____61931 = sizeof t1  in
        let uu____61933 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____61948  ->
                 match uu____61948 with
                 | (bv,uu____61958) ->
                     let uu____61963 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____61963) (Prims.parse_int "0") bs
           in
        uu____61931 + uu____61933
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____61992 = sizeof hd1  in
        let uu____61994 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____62009  ->
                 match uu____62009 with
                 | (arg,uu____62019) ->
                     let uu____62024 = sizeof arg  in acc + uu____62024)
            (Prims.parse_int "0") args
           in
        uu____61992 + uu____61994
    | uu____62027 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____62041 =
        let uu____62042 = un_uinst t  in uu____62042.FStar_Syntax_Syntax.n
         in
      match uu____62041 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____62047 -> false
  
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
        let uu____62096 = FStar_Options.set_options t s  in
        match uu____62096 with
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
          ((let uu____62113 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____62113 (fun a1  -> ()));
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
          let uu____62128 = FStar_Options.internal_pop ()  in
          if uu____62128
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
    | FStar_Syntax_Syntax.Tm_delayed uu____62160 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____62187 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____62202 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____62203 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____62204 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____62213) ->
        let uu____62238 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____62238 with
         | (bs1,t2) ->
             let uu____62247 =
               FStar_List.collect
                 (fun uu____62259  ->
                    match uu____62259 with
                    | (b,uu____62269) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62274 = unbound_variables t2  in
             FStar_List.append uu____62247 uu____62274)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____62299 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____62299 with
         | (bs1,c1) ->
             let uu____62308 =
               FStar_List.collect
                 (fun uu____62320  ->
                    match uu____62320 with
                    | (b,uu____62330) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62335 = unbound_variables_comp c1  in
             FStar_List.append uu____62308 uu____62335)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____62344 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____62344 with
         | (bs,t2) ->
             let uu____62367 =
               FStar_List.collect
                 (fun uu____62379  ->
                    match uu____62379 with
                    | (b1,uu____62389) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____62394 = unbound_variables t2  in
             FStar_List.append uu____62367 uu____62394)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____62423 =
          FStar_List.collect
            (fun uu____62437  ->
               match uu____62437 with
               | (x,uu____62449) -> unbound_variables x) args
           in
        let uu____62458 = unbound_variables t1  in
        FStar_List.append uu____62423 uu____62458
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____62499 = unbound_variables t1  in
        let uu____62502 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____62517 = FStar_Syntax_Subst.open_branch br  in
                  match uu____62517 with
                  | (p,wopt,t2) ->
                      let uu____62539 = unbound_variables t2  in
                      let uu____62542 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____62539 uu____62542))
           in
        FStar_List.append uu____62499 uu____62502
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____62556) ->
        let uu____62597 = unbound_variables t1  in
        let uu____62600 =
          let uu____62603 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____62634 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____62603 uu____62634  in
        FStar_List.append uu____62597 uu____62600
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____62675 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____62678 =
          let uu____62681 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____62684 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____62689 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____62691 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____62691 with
                 | (uu____62712,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____62681 uu____62684  in
        FStar_List.append uu____62675 uu____62678
    | FStar_Syntax_Syntax.Tm_let ((uu____62714,lbs),t1) ->
        let uu____62734 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____62734 with
         | (lbs1,t2) ->
             let uu____62749 = unbound_variables t2  in
             let uu____62752 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____62759 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____62762 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____62759 uu____62762) lbs1
                in
             FStar_List.append uu____62749 uu____62752)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____62779 = unbound_variables t1  in
        let uu____62782 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____62821  ->
                      match uu____62821 with
                      | (a,uu____62833) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____62842,uu____62843,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____62849,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____62855 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____62864 -> []
          | FStar_Syntax_Syntax.Meta_named uu____62865 -> []  in
        FStar_List.append uu____62779 uu____62782

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____62872) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____62882) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____62892 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____62895 =
          FStar_List.collect
            (fun uu____62909  ->
               match uu____62909 with
               | (a,uu____62921) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____62892 uu____62895

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
            let uu____63036 = head_and_args h  in
            (match uu____63036 with
             | (head1,args) ->
                 let uu____63097 =
                   let uu____63098 = FStar_Syntax_Subst.compress head1  in
                   uu____63098.FStar_Syntax_Syntax.n  in
                 (match uu____63097 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____63151 -> aux (h :: acc) t))
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
      let uu____63175 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____63175 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2985_63217 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2985_63217.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2985_63217.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2985_63217.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2985_63217.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  