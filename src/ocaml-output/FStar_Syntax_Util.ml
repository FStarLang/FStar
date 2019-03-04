open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____44953 = FStar_ST.op_Bang tts_f  in
    match uu____44953 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____45017 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____45017 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____45024 =
      let uu____45027 =
        let uu____45030 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____45030]  in
      FStar_List.append lid.FStar_Ident.ns uu____45027  in
    FStar_Ident.lid_of_ids uu____45024
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____45048 .
    (FStar_Syntax_Syntax.bv * 'Auu____45048) ->
      (FStar_Syntax_Syntax.term * 'Auu____45048)
  =
  fun uu____45061  ->
    match uu____45061 with
    | (b,imp) ->
        let uu____45068 = FStar_Syntax_Syntax.bv_to_name b  in
        (uu____45068, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____45120 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____45120
            then []
            else
              (let uu____45139 = arg_of_non_null_binder b  in [uu____45139])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____45174 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____45256 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45256
              then
                let b1 =
                  let uu____45282 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____45282, (FStar_Pervasives_Native.snd b))  in
                let uu____45289 = arg_of_non_null_binder b1  in
                (b1, uu____45289)
              else
                (let uu____45312 = arg_of_non_null_binder b  in
                 (b, uu____45312))))
       in
    FStar_All.pipe_right uu____45174 FStar_List.unzip
  
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
              let uu____45446 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45446
              then
                let uu____45455 = b  in
                match uu____45455 with
                | (a,imp) ->
                    let b1 =
                      let uu____45475 =
                        let uu____45477 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____45477  in
                      FStar_Ident.id_of_text uu____45475  in
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
        let uu____45522 =
          let uu____45529 =
            let uu____45530 =
              let uu____45545 = name_binders binders  in (uu____45545, comp)
               in
            FStar_Syntax_Syntax.Tm_arrow uu____45530  in
          FStar_Syntax_Syntax.mk uu____45529  in
        uu____45522 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____45567 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45604  ->
            match uu____45604 with
            | (t,imp) ->
                let uu____45615 =
                  let uu____45616 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____45616
                   in
                (uu____45615, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45671  ->
            match uu____45671 with
            | (t,imp) ->
                let uu____45688 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____45688, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____45701 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____45701
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____45713 . 'Auu____45713 -> 'Auu____45713 Prims.list =
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
          (fun uu____45839  ->
             fun uu____45840  ->
               match (uu____45839, uu____45840) with
               | ((x,uu____45866),(y,uu____45868)) ->
                   let uu____45889 =
                     let uu____45896 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____45896)  in
                   FStar_Syntax_Syntax.NT uu____45889) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____45912) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45918,uu____45919) ->
        unmeta e2
    | uu____45960 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____45974 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____45981 -> e1
         | uu____45990 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45992,uu____45993) ->
        unmeta_safe e2
    | uu____46034 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____46053 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____46056 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____46070 = univ_kernel u1  in
        (match uu____46070 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____46087 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____46096 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____46111 = univ_kernel u  in
    FStar_Pervasives_Native.snd uu____46111
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____46131,uu____46132) ->
          failwith "Impossible: compare_univs"
      | (uu____46136,FStar_Syntax_Syntax.U_bvar uu____46137) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____46142) ->
          ~- (Prims.parse_int "1")
      | (uu____46144,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____46147) -> ~- (Prims.parse_int "1")
      | (uu____46149,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____46153,FStar_Syntax_Syntax.U_unif
         uu____46154) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____46164,FStar_Syntax_Syntax.U_name
         uu____46165) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____46193 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____46195 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____46193 - uu____46195
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____46231 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____46231
                 (fun uu____46247  ->
                    match uu____46247 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____46275,uu____46276) ->
          ~- (Prims.parse_int "1")
      | (uu____46280,FStar_Syntax_Syntax.U_max uu____46281) ->
          (Prims.parse_int "1")
      | uu____46285 ->
          let uu____46290 = univ_kernel u1  in
          (match uu____46290 with
           | (k1,n1) ->
               let uu____46301 = univ_kernel u2  in
               (match uu____46301 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____46332 = compare_univs u1 u2  in
      uu____46332 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____46351 =
        let uu____46352 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____46352;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____46351
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____46372 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____46381 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____46404 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____46413 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____46440 =
          let uu____46441 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46441  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46440;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____46470 =
          let uu____46471 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46471  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46470;
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
      let uu___631_46507 = c  in
      let uu____46508 =
        let uu____46509 =
          let uu___633_46510 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___633_46510.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___633_46510.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___633_46510.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___633_46510.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____46509  in
      {
        FStar_Syntax_Syntax.n = uu____46508;
        FStar_Syntax_Syntax.pos = (uu___631_46507.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___631_46507.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____46536 -> c
        | FStar_Syntax_Syntax.GTotal uu____46545 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___645_46556 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___645_46556.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___645_46556.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___645_46556.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___645_46556.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___648_46557 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___648_46557.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___648_46557.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____46560  ->
           let uu____46561 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____46561)
  
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
    | uu____46601 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____46616 -> true
    | FStar_Syntax_Syntax.GTotal uu____46626 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___402_46651  ->
               match uu___402_46651 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46655 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___403_46668  ->
               match uu___403_46668 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46672 -> false)))
  
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
            (fun uu___404_46685  ->
               match uu___404_46685 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46689 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___405_46706  ->
            match uu___405_46706 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46710 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___406_46723  ->
            match uu___406_46723 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46727 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____46759 -> true
    | FStar_Syntax_Syntax.GTotal uu____46769 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___407_46784  ->
                   match uu___407_46784 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____46787 -> false)))
  
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
            (fun uu___408_46832  ->
               match uu___408_46832 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____46835 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46851 =
      let uu____46852 = FStar_Syntax_Subst.compress t  in
      uu____46852.FStar_Syntax_Syntax.n  in
    match uu____46851 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46856,c) -> is_pure_or_ghost_comp c
    | uu____46878 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____46893 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46902 =
      let uu____46903 = FStar_Syntax_Subst.compress t  in
      uu____46903.FStar_Syntax_Syntax.n  in
    match uu____46902 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46907,c) -> is_lemma_comp c
    | uu____46929 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____46937 =
      let uu____46938 = FStar_Syntax_Subst.compress t  in
      uu____46938.FStar_Syntax_Syntax.n  in
    match uu____46937 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____46942) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____46968) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____47005,t1,uu____47007) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____47033,uu____47034) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____47076) -> head_of t1
    | uu____47081 -> t
  
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
    | uu____47159 -> (t1, [])
  
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
        let uu____47241 = head_and_args' head1  in
        (match uu____47241 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____47310 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____47337) ->
        FStar_Syntax_Subst.compress t2
    | uu____47342 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____47350 =
      let uu____47351 = FStar_Syntax_Subst.compress t  in
      uu____47351.FStar_Syntax_Syntax.n  in
    match uu____47350 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____47355,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____47383)::uu____47384 ->
                  let pats' = unmeta pats  in
                  let uu____47444 = head_and_args pats'  in
                  (match uu____47444 with
                   | (head1,uu____47463) ->
                       let uu____47488 =
                         let uu____47489 = un_uinst head1  in
                         uu____47489.FStar_Syntax_Syntax.n  in
                       (match uu____47488 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____47494 -> false))
              | uu____47496 -> false)
         | uu____47508 -> false)
    | uu____47510 -> false
  
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
                (fun uu___409_47529  ->
                   match uu___409_47529 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____47532 -> false)))
    | uu____47534 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____47551) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____47561) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____47590 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____47599 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___827_47611 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___827_47611.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___827_47611.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___827_47611.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___827_47611.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____47625  ->
           let uu____47626 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____47626 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___410_47644  ->
            match uu___410_47644 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____47648 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____47656 -> []
    | FStar_Syntax_Syntax.GTotal uu____47673 -> []
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
    | uu____47717 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____47727,uu____47728) ->
        unascribe e2
    | uu____47769 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____47822,uu____47823) ->
          ascribe t' k
      | uu____47864 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____47891 =
      let uu____47900 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____47900  in
    uu____47891 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47956 =
      let uu____47957 = FStar_Syntax_Subst.compress t  in
      uu____47957.FStar_Syntax_Syntax.n  in
    match uu____47956 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____47961 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____47961
    | uu____47962 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47969 =
      let uu____47970 = FStar_Syntax_Subst.compress t  in
      uu____47970.FStar_Syntax_Syntax.n  in
    match uu____47969 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____47974 ->
             let uu____47983 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____47983
         | uu____47984 -> t)
    | uu____47985 -> t
  
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
      | uu____48009 -> false
  
let rec unlazy_as_t :
  'Auu____48022 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_Syntax_Syntax.term -> 'Auu____48022
  =
  fun k  ->
    fun t  ->
      let uu____48033 =
        let uu____48034 = FStar_Syntax_Subst.compress t  in
        uu____48034.FStar_Syntax_Syntax.n  in
      match uu____48033 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____48039;
            FStar_Syntax_Syntax.rng = uu____48040;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____48043 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____48084 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____48084;
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
    let uu____48097 =
      let uu____48112 = unascribe t  in head_and_args' uu____48112  in
    match uu____48097 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____48146 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____48157 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____48168 -> false
  
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
      | (NotEqual ,uu____48218) -> NotEqual
      | (uu____48219,NotEqual ) -> NotEqual
      | (Unknown ,uu____48220) -> Unknown
      | (uu____48221,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___411_48342 = if uu___411_48342 then Equal else Unknown
         in
      let equal_iff uu___412_48353 =
        if uu___412_48353 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____48374 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____48396 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____48396
        then
          let uu____48400 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____48477  ->
                    match uu____48477 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____48518 = eq_tm a1 a2  in
                        eq_inj acc uu____48518) Equal) uu____48400
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____48532 =
          let uu____48549 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____48549 head_and_args  in
        match uu____48532 with
        | (head1,args1) ->
            let uu____48602 =
              let uu____48619 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____48619 head_and_args  in
            (match uu____48602 with
             | (head2,args2) ->
                 let uu____48672 =
                   let uu____48677 =
                     let uu____48678 = un_uinst head1  in
                     uu____48678.FStar_Syntax_Syntax.n  in
                   let uu____48681 =
                     let uu____48682 = un_uinst head2  in
                     uu____48682.FStar_Syntax_Syntax.n  in
                   (uu____48677, uu____48681)  in
                 (match uu____48672 with
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
                  | uu____48709 -> FStar_Pervasives_Native.None))
         in
      let uu____48722 =
        let uu____48727 =
          let uu____48728 = unmeta t11  in uu____48728.FStar_Syntax_Syntax.n
           in
        let uu____48731 =
          let uu____48732 = unmeta t21  in uu____48732.FStar_Syntax_Syntax.n
           in
        (uu____48727, uu____48731)  in
      match uu____48722 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____48738,uu____48739) ->
          let uu____48740 = unlazy t11  in eq_tm uu____48740 t21
      | (uu____48741,FStar_Syntax_Syntax.Tm_lazy uu____48742) ->
          let uu____48743 = unlazy t21  in eq_tm t11 uu____48743
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____48746 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____48770 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____48770
            (fun uu____48818  ->
               match uu____48818 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____48833 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____48833
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____48847 = eq_tm f g  in
          eq_and uu____48847
            (fun uu____48850  ->
               let uu____48851 = eq_univs_list us vs  in equal_if uu____48851)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48853),uu____48854) -> Unknown
      | (uu____48855,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48856)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____48859 = FStar_Const.eq_const c d  in
          equal_iff uu____48859
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____48862)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____48864))) ->
          let uu____48893 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____48893
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____48947 =
            let uu____48952 =
              let uu____48953 = un_uinst h1  in
              uu____48953.FStar_Syntax_Syntax.n  in
            let uu____48956 =
              let uu____48957 = un_uinst h2  in
              uu____48957.FStar_Syntax_Syntax.n  in
            (uu____48952, uu____48956)  in
          (match uu____48947 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____48963 =
                    let uu____48965 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____48965  in
                  FStar_List.mem uu____48963 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____48967 ->
               let uu____48972 = eq_tm h1 h2  in
               eq_and uu____48972 (fun uu____48974  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____49080 = FStar_List.zip bs1 bs2  in
            let uu____49143 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____49180  ->
                 fun a  ->
                   match uu____49180 with
                   | (b1,b2) ->
                       eq_and a (fun uu____49273  -> branch_matches b1 b2))
              uu____49080 uu____49143
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____49278 = eq_univs u v1  in equal_if uu____49278
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____49292 = eq_quoteinfo q1 q2  in
          eq_and uu____49292 (fun uu____49294  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____49307 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____49307 (fun uu____49309  -> eq_tm phi1 phi2)
      | uu____49310 -> Unknown

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
      | ([],uu____49382) -> NotEqual
      | (uu____49413,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____49505 = eq_tm t1 t2  in
             match uu____49505 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____49506 = eq_antiquotes a11 a21  in
                 (match uu____49506 with
                  | NotEqual  -> NotEqual
                  | uu____49507 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____49522) -> NotEqual
      | (uu____49529,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____49559 -> NotEqual

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
        | (uu____49651,uu____49652) -> false  in
      let uu____49662 = b1  in
      match uu____49662 with
      | (p1,w1,t1) ->
          let uu____49696 = b2  in
          (match uu____49696 with
           | (p2,w2,t2) ->
               let uu____49730 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____49730
               then
                 let uu____49733 =
                   (let uu____49737 = eq_tm t1 t2  in uu____49737 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____49746 = eq_tm t11 t21  in
                             uu____49746 = Equal) w1 w2)
                    in
                 (if uu____49733 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____49811)::a11,(b,uu____49814)::b1) ->
          let uu____49888 = eq_tm a b  in
          (match uu____49888 with
           | Equal  -> eq_args a11 b1
           | uu____49889 -> Unknown)
      | uu____49890 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____49926) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____49932,uu____49933) ->
        unrefine t2
    | uu____49974 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____49982 =
      let uu____49983 = FStar_Syntax_Subst.compress t  in
      uu____49983.FStar_Syntax_Syntax.n  in
    match uu____49982 with
    | FStar_Syntax_Syntax.Tm_uvar uu____49987 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50002) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____50007 ->
        let uu____50024 =
          let uu____50025 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____50025 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____50024 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____50088,uu____50089) ->
        is_uvar t1
    | uu____50130 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50139 =
      let uu____50140 = unrefine t  in uu____50140.FStar_Syntax_Syntax.n  in
    match uu____50139 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50146) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50172) -> is_unit t1
    | uu____50177 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50186 =
      let uu____50187 = FStar_Syntax_Subst.compress t  in
      uu____50187.FStar_Syntax_Syntax.n  in
    match uu____50186 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____50192 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50201 =
      let uu____50202 = unrefine t  in uu____50202.FStar_Syntax_Syntax.n  in
    match uu____50201 with
    | FStar_Syntax_Syntax.Tm_type uu____50206 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50210) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50236) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____50241,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____50263 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____50272 =
      let uu____50273 = FStar_Syntax_Subst.compress e  in
      uu____50273.FStar_Syntax_Syntax.n  in
    match uu____50272 with
    | FStar_Syntax_Syntax.Tm_abs uu____50277 -> true
    | uu____50297 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50306 =
      let uu____50307 = FStar_Syntax_Subst.compress t  in
      uu____50307.FStar_Syntax_Syntax.n  in
    match uu____50306 with
    | FStar_Syntax_Syntax.Tm_arrow uu____50311 -> true
    | uu____50327 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____50337) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____50343,uu____50344) ->
        pre_typ t2
    | uu____50385 -> t1
  
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
      let uu____50410 =
        let uu____50411 = un_uinst typ1  in uu____50411.FStar_Syntax_Syntax.n
         in
      match uu____50410 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____50476 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____50506 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____50527,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____50534) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____50539,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____50550,uu____50551,uu____50552,uu____50553,uu____50554) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____50564,uu____50565,uu____50566,uu____50567) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____50573,uu____50574,uu____50575,uu____50576,uu____50577) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____50585,uu____50586) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____50588,uu____50589) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____50592 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____50593 -> []
    | FStar_Syntax_Syntax.Sig_main uu____50594 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____50608 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___413_50634  ->
    match uu___413_50634 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____50648 'Auu____50649 .
    ('Auu____50648 FStar_Syntax_Syntax.syntax * 'Auu____50649) ->
      FStar_Range.range
  =
  fun uu____50660  ->
    match uu____50660 with | (hd1,uu____50668) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____50682 'Auu____50683 .
    ('Auu____50682 FStar_Syntax_Syntax.syntax * 'Auu____50683) Prims.list ->
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
      | uu____50781 ->
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
      let uu____50840 =
        FStar_List.map
          (fun uu____50867  ->
             match uu____50867 with
             | (bv,aq) ->
                 let uu____50886 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____50886, aq)) bs
         in
      mk_app f uu____50840
  
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
          let uu____50936 = FStar_Ident.range_of_lid l  in
          let uu____50937 =
            let uu____50946 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____50946  in
          uu____50937 FStar_Pervasives_Native.None uu____50936
      | uu____50954 ->
          let e =
            let uu____50968 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____50968 args  in
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
          let uu____51045 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____51045
          then
            let uu____51048 =
              let uu____51054 =
                let uu____51056 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____51056  in
              let uu____51059 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____51054, uu____51059)  in
            FStar_Ident.mk_ident uu____51048
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___1421_51064 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___1421_51064.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___1421_51064.FStar_Syntax_Syntax.sort)
          }  in
        let uu____51065 = mk_field_projector_name_from_ident lid nm  in
        (uu____51065, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____51077) -> ses
    | uu____51086 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____51097 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____51110 = FStar_Syntax_Unionfind.find uv  in
      match uu____51110 with
      | FStar_Pervasives_Native.Some uu____51113 ->
          let uu____51114 =
            let uu____51116 =
              let uu____51118 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____51118  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____51116  in
          failwith uu____51114
      | uu____51123 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____51206 -> q1 = q2
  
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
              let uu____51252 =
                let uu___1482_51253 = rc  in
                let uu____51254 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1482_51253.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____51254;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1482_51253.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____51252
           in
        match bs with
        | [] -> t
        | uu____51271 ->
            let body =
              let uu____51273 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____51273  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____51303 =
                   let uu____51310 =
                     let uu____51311 =
                       let uu____51330 =
                         let uu____51339 =
                           FStar_Syntax_Subst.close_binders bs  in
                         FStar_List.append uu____51339 bs'  in
                       let uu____51354 = close_lopt lopt'  in
                       (uu____51330, t1, uu____51354)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51311  in
                   FStar_Syntax_Syntax.mk uu____51310  in
                 uu____51303 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____51372 ->
                 let uu____51373 =
                   let uu____51380 =
                     let uu____51381 =
                       let uu____51400 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____51409 = close_lopt lopt  in
                       (uu____51400, body, uu____51409)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51381  in
                   FStar_Syntax_Syntax.mk uu____51380  in
                 uu____51373 FStar_Pervasives_Native.None
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
      | uu____51468 ->
          let uu____51477 =
            let uu____51484 =
              let uu____51485 =
                let uu____51500 = FStar_Syntax_Subst.close_binders bs  in
                let uu____51509 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____51500, uu____51509)  in
              FStar_Syntax_Syntax.Tm_arrow uu____51485  in
            FStar_Syntax_Syntax.mk uu____51484  in
          uu____51477 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____51561 =
        let uu____51562 = FStar_Syntax_Subst.compress t  in
        uu____51562.FStar_Syntax_Syntax.n  in
      match uu____51561 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____51592) ->
               let uu____51601 =
                 let uu____51602 = FStar_Syntax_Subst.compress tres  in
                 uu____51602.FStar_Syntax_Syntax.n  in
               (match uu____51601 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____51645 -> t)
           | uu____51646 -> t)
      | uu____51647 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____51665 =
        let uu____51666 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____51666 t.FStar_Syntax_Syntax.pos  in
      let uu____51667 =
        let uu____51674 =
          let uu____51675 =
            let uu____51682 =
              let uu____51685 =
                let uu____51686 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____51686]  in
              FStar_Syntax_Subst.close uu____51685 t  in
            (b, uu____51682)  in
          FStar_Syntax_Syntax.Tm_refine uu____51675  in
        FStar_Syntax_Syntax.mk uu____51674  in
      uu____51667 FStar_Pervasives_Native.None uu____51665
  
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
        let uu____51769 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____51769 with
         | (bs1,c1) ->
             let uu____51788 = is_total_comp c1  in
             if uu____51788
             then
               let uu____51803 = arrow_formals_comp (comp_result c1)  in
               (match uu____51803 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____51870;
           FStar_Syntax_Syntax.index = uu____51871;
           FStar_Syntax_Syntax.sort = s;_},uu____51873)
        ->
        let rec aux s1 k2 =
          let uu____51904 =
            let uu____51905 = FStar_Syntax_Subst.compress s1  in
            uu____51905.FStar_Syntax_Syntax.n  in
          match uu____51904 with
          | FStar_Syntax_Syntax.Tm_arrow uu____51920 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____51935;
                 FStar_Syntax_Syntax.index = uu____51936;
                 FStar_Syntax_Syntax.sort = s2;_},uu____51938)
              -> aux s2 k2
          | uu____51946 ->
              let uu____51947 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____51947)
           in
        aux s k1
    | uu____51962 ->
        let uu____51963 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____51963)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____51998 = arrow_formals_comp k  in
    match uu____51998 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____52140 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____52140 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____52164 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___414_52173  ->
                         match uu___414_52173 with
                         | FStar_Syntax_Syntax.DECREASES uu____52175 -> true
                         | uu____52179 -> false))
                  in
               (match uu____52164 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____52214 ->
                    let uu____52217 = is_total_comp c1  in
                    if uu____52217
                    then
                      let uu____52236 =
                        arrow_until_decreases (comp_result c1)  in
                      (match uu____52236 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____52329;
             FStar_Syntax_Syntax.index = uu____52330;
             FStar_Syntax_Syntax.sort = k2;_},uu____52332)
          -> arrow_until_decreases k2
      | uu____52340 -> ([], FStar_Pervasives_Native.None)  in
    let uu____52361 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____52361 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____52415 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____52436 =
                 FStar_Common.tabulate n_univs (fun uu____52446  -> false)
                  in
               let uu____52449 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____52474  ->
                         match uu____52474 with
                         | (x,uu____52483) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____52436 uu____52449)
           in
        ((n_univs + (FStar_List.length bs)), uu____52415)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____52545 =
            let uu___1604_52546 = rc  in
            let uu____52547 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1604_52546.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____52547;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1604_52546.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____52545
      | uu____52556 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____52590 =
        let uu____52591 =
          let uu____52594 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____52594  in
        uu____52591.FStar_Syntax_Syntax.n  in
      match uu____52590 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____52640 = aux t2 what  in
          (match uu____52640 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____52712 -> ([], t1, abs_body_lcomp)  in
    let uu____52729 = aux t FStar_Pervasives_Native.None  in
    match uu____52729 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____52777 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____52777 with
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
                    | (FStar_Pervasives_Native.None ,uu____52940) -> def
                    | (uu____52951,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____52963) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _52979  ->
                                  FStar_Syntax_Syntax.U_name _52979))
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
            let uu____53061 = FStar_Syntax_Subst.open_univ_vars_comp uvs c
               in
            (match uu____53061 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____53096 ->
            let t' = arrow binders c  in
            let uu____53108 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____53108 with
             | (uvs1,t'1) ->
                 let uu____53129 =
                   let uu____53130 = FStar_Syntax_Subst.compress t'1  in
                   uu____53130.FStar_Syntax_Syntax.n  in
                 (match uu____53129 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____53179 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____53204 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____53215 -> false
  
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
      let uu____53278 =
        let uu____53279 = pre_typ t  in uu____53279.FStar_Syntax_Syntax.n  in
      match uu____53278 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____53284 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____53298 =
        let uu____53299 = pre_typ t  in uu____53299.FStar_Syntax_Syntax.n  in
      match uu____53298 with
      | FStar_Syntax_Syntax.Tm_fvar uu____53303 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____53305) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____53331) ->
          is_constructed_typ t1 lid
      | uu____53336 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____53349 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____53350 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____53351 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____53353) -> get_tycon t2
    | uu____53378 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____53386 =
      let uu____53387 = un_uinst t  in uu____53387.FStar_Syntax_Syntax.n  in
    match uu____53386 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____53392 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____53406 =
        let uu____53410 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____53410  in
      match uu____53406 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____53442 -> false
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
  fun uu____53461  ->
    let u =
      let uu____53467 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _53484  -> FStar_Syntax_Syntax.U_unif _53484)
        uu____53467
       in
    let uu____53485 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____53485, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____53498 = eq_tm a a'  in
      match uu____53498 with | Equal  -> true | uu____53501 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____53506 =
    let uu____53513 =
      let uu____53514 =
        let uu____53515 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____53515
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____53514  in
    FStar_Syntax_Syntax.mk uu____53513  in
  uu____53506 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____53630 =
            let uu____53633 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____53634 =
              let uu____53641 =
                let uu____53642 =
                  let uu____53659 =
                    let uu____53670 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____53679 =
                      let uu____53690 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____53690]  in
                    uu____53670 :: uu____53679  in
                  (tand, uu____53659)  in
                FStar_Syntax_Syntax.Tm_app uu____53642  in
              FStar_Syntax_Syntax.mk uu____53641  in
            uu____53634 FStar_Pervasives_Native.None uu____53633  in
          FStar_Pervasives_Native.Some uu____53630
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____53770 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____53771 =
          let uu____53778 =
            let uu____53779 =
              let uu____53796 =
                let uu____53807 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____53816 =
                  let uu____53827 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____53827]  in
                uu____53807 :: uu____53816  in
              (op_t, uu____53796)  in
            FStar_Syntax_Syntax.Tm_app uu____53779  in
          FStar_Syntax_Syntax.mk uu____53778  in
        uu____53771 FStar_Pervasives_Native.None uu____53770
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____53887 =
      let uu____53894 =
        let uu____53895 =
          let uu____53912 =
            let uu____53923 = FStar_Syntax_Syntax.as_arg phi  in
            [uu____53923]  in
          (t_not, uu____53912)  in
        FStar_Syntax_Syntax.Tm_app uu____53895  in
      FStar_Syntax_Syntax.mk uu____53894  in
    uu____53887 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____54123 =
      let uu____54130 =
        let uu____54131 =
          let uu____54148 =
            let uu____54159 = FStar_Syntax_Syntax.as_arg e  in [uu____54159]
             in
          (b2t_v, uu____54148)  in
        FStar_Syntax_Syntax.Tm_app uu____54131  in
      FStar_Syntax_Syntax.mk uu____54130  in
    uu____54123 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____54206 =
      let uu____54207 = unmeta t  in uu____54207.FStar_Syntax_Syntax.n  in
    match uu____54206 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____54212 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54235 = is_t_true t1  in
      if uu____54235
      then t2
      else
        (let uu____54242 = is_t_true t2  in
         if uu____54242 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54270 = is_t_true t1  in
      if uu____54270
      then t_true
      else
        (let uu____54277 = is_t_true t2  in
         if uu____54277 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____54306 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____54307 =
        let uu____54314 =
          let uu____54315 =
            let uu____54332 =
              let uu____54343 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____54352 =
                let uu____54363 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____54363]  in
              uu____54343 :: uu____54352  in
            (teq, uu____54332)  in
          FStar_Syntax_Syntax.Tm_app uu____54315  in
        FStar_Syntax_Syntax.mk uu____54314  in
      uu____54307 FStar_Pervasives_Native.None uu____54306
  
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
          let uu____54433 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____54434 =
            let uu____54441 =
              let uu____54442 =
                let uu____54459 =
                  let uu____54470 = FStar_Syntax_Syntax.iarg t  in
                  let uu____54479 =
                    let uu____54490 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____54499 =
                      let uu____54510 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____54510]  in
                    uu____54490 :: uu____54499  in
                  uu____54470 :: uu____54479  in
                (eq_inst, uu____54459)  in
              FStar_Syntax_Syntax.Tm_app uu____54442  in
            FStar_Syntax_Syntax.mk uu____54441  in
          uu____54434 FStar_Pervasives_Native.None uu____54433
  
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
        let uu____54590 =
          let uu____54597 =
            let uu____54598 =
              let uu____54615 =
                let uu____54626 = FStar_Syntax_Syntax.iarg t  in
                let uu____54635 =
                  let uu____54646 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____54655 =
                    let uu____54666 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____54666]  in
                  uu____54646 :: uu____54655  in
                uu____54626 :: uu____54635  in
              (t_has_type1, uu____54615)  in
            FStar_Syntax_Syntax.Tm_app uu____54598  in
          FStar_Syntax_Syntax.mk uu____54597  in
        uu____54590 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____54746 =
          let uu____54753 =
            let uu____54754 =
              let uu____54771 =
                let uu____54782 = FStar_Syntax_Syntax.iarg t  in
                let uu____54791 =
                  let uu____54802 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____54802]  in
                uu____54782 :: uu____54791  in
              (t_with_type1, uu____54771)  in
            FStar_Syntax_Syntax.Tm_app uu____54754  in
          FStar_Syntax_Syntax.mk uu____54753  in
        uu____54746 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____54852 =
    let uu____54859 =
      let uu____54860 =
        let uu____54867 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____54867, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____54860  in
    FStar_Syntax_Syntax.mk uu____54859  in
  uu____54852 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____54885 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____54898 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____54909 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____54885 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____54930  -> c0)
  
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
        let uu____55013 =
          let uu____55020 =
            let uu____55021 =
              let uu____55038 =
                let uu____55049 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____55058 =
                  let uu____55069 =
                    let uu____55078 =
                      let uu____55079 =
                        let uu____55080 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____55080]  in
                      abs uu____55079 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____55078  in
                  [uu____55069]  in
                uu____55049 :: uu____55058  in
              (fa, uu____55038)  in
            FStar_Syntax_Syntax.Tm_app uu____55021  in
          FStar_Syntax_Syntax.mk uu____55020  in
        uu____55013 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____55210 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____55210
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____55229 -> true
    | uu____55231 -> false
  
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
          let uu____55278 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____55278, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____55307 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____55307, FStar_Pervasives_Native.None, t2)  in
        let uu____55321 =
          let uu____55322 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____55322  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____55321
  
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
      let uu____55398 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55401 =
        let uu____55412 = FStar_Syntax_Syntax.as_arg p  in [uu____55412]  in
      mk_app uu____55398 uu____55401
  
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
      let uu____55452 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55455 =
        let uu____55466 = FStar_Syntax_Syntax.as_arg p  in [uu____55466]  in
      mk_app uu____55452 uu____55455
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55501 = head_and_args t  in
    match uu____55501 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____55550 =
          let uu____55565 =
            let uu____55566 = FStar_Syntax_Subst.compress head3  in
            uu____55566.FStar_Syntax_Syntax.n  in
          (uu____55565, args)  in
        (match uu____55550 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____55585)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____55651 =
                    let uu____55656 =
                      let uu____55657 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____55657]  in
                    FStar_Syntax_Subst.open_term uu____55656 p  in
                  (match uu____55651 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____55714 -> failwith "impossible"  in
                       let uu____55722 =
                         let uu____55724 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____55724
                          in
                       if uu____55722
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____55740 -> FStar_Pervasives_Native.None)
         | uu____55743 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55774 = head_and_args t  in
    match uu____55774 with
    | (head1,args) ->
        let uu____55825 =
          let uu____55840 =
            let uu____55841 = FStar_Syntax_Subst.compress head1  in
            uu____55841.FStar_Syntax_Syntax.n  in
          (uu____55840, args)  in
        (match uu____55825 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____55863;
               FStar_Syntax_Syntax.vars = uu____55864;_},u::[]),(t1,uu____55867)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____55914 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55949 = head_and_args t  in
    match uu____55949 with
    | (head1,args) ->
        let uu____56000 =
          let uu____56015 =
            let uu____56016 = FStar_Syntax_Subst.compress head1  in
            uu____56016.FStar_Syntax_Syntax.n  in
          (uu____56015, args)  in
        (match uu____56000 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____56038;
               FStar_Syntax_Syntax.vars = uu____56039;_},u::[]),(t1,uu____56042)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____56089 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____56117 =
      let uu____56134 = unmeta t  in head_and_args uu____56134  in
    match uu____56117 with
    | (head1,uu____56137) ->
        let uu____56162 =
          let uu____56163 = un_uinst head1  in
          uu____56163.FStar_Syntax_Syntax.n  in
        (match uu____56162 with
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
         | uu____56168 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____56188 =
      let uu____56201 =
        let uu____56202 = FStar_Syntax_Subst.compress t  in
        uu____56202.FStar_Syntax_Syntax.n  in
      match uu____56201 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____56332 =
            let uu____56343 =
              let uu____56344 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____56344  in
            (b, uu____56343)  in
          FStar_Pervasives_Native.Some uu____56332
      | uu____56361 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____56188
      (fun uu____56399  ->
         match uu____56399 with
         | (b,c) ->
             let uu____56436 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____56436 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____56499 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____56536 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____56536
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____56588 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____56632 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____56674 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____56714) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____56726) ->
          unmeta_monadic t
      | uu____56739 -> f2  in
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
      let aux f2 uu____56835 =
        match uu____56835 with
        | (lid,arity) ->
            let uu____56844 =
              let uu____56861 = unmeta_monadic f2  in
              head_and_args uu____56861  in
            (match uu____56844 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____56891 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____56891
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____56971 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____56971)
      | uu____56984 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____57051 = head_and_args t1  in
        match uu____57051 with
        | (t2,args) ->
            let uu____57106 = un_uinst t2  in
            let uu____57107 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____57148  ->
                      match uu____57148 with
                      | (t3,imp) ->
                          let uu____57167 = unascribe t3  in
                          (uu____57167, imp)))
               in
            (uu____57106, uu____57107)
         in
      let rec aux qopt out t1 =
        let uu____57218 = let uu____57242 = flat t1  in (qopt, uu____57242)
           in
        match uu____57218 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57282;
                 FStar_Syntax_Syntax.vars = uu____57283;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____57286);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____57287;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____57288;_},uu____57289)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57391;
                 FStar_Syntax_Syntax.vars = uu____57392;_},uu____57393::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____57396);
                  FStar_Syntax_Syntax.pos = uu____57397;
                  FStar_Syntax_Syntax.vars = uu____57398;_},uu____57399)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57516;
               FStar_Syntax_Syntax.vars = uu____57517;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____57520);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____57521;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____57522;_},uu____57523)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57616 =
              let uu____57620 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57620  in
            aux uu____57616 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57630;
               FStar_Syntax_Syntax.vars = uu____57631;_},uu____57632::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____57635);
                FStar_Syntax_Syntax.pos = uu____57636;
                FStar_Syntax_Syntax.vars = uu____57637;_},uu____57638)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57747 =
              let uu____57751 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57751  in
            aux uu____57747 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____57761) ->
            let bs = FStar_List.rev out  in
            let uu____57814 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____57814 with
             | (bs1,t2) ->
                 let uu____57823 = patterns t2  in
                 (match uu____57823 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____57873 -> FStar_Pervasives_Native.None  in
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
      let uu____57965 = un_squash t  in
      FStar_Util.bind_opt uu____57965
        (fun t1  ->
           let uu____57981 = head_and_args' t1  in
           match uu____57981 with
           | (hd1,args) ->
               let uu____58020 =
                 let uu____58026 =
                   let uu____58027 = un_uinst hd1  in
                   uu____58027.FStar_Syntax_Syntax.n  in
                 (uu____58026, (FStar_List.length args))  in
               (match uu____58020 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58043) when
                    (_58043 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58046) when
                    (_58046 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58049) when
                    (_58049 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58052) when
                    (_58052 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58055) when
                    (_58055 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58058) when
                    (_58058 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58061) when
                    (_58061 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58064) when
                    (_58064 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____58065 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____58095 = un_squash t  in
      FStar_Util.bind_opt uu____58095
        (fun t1  ->
           let uu____58110 = arrow_one t1  in
           match uu____58110 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____58125 =
                 let uu____58127 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____58127  in
               if uu____58125
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____58137 = comp_to_comp_typ_nouniv c  in
                    uu____58137.FStar_Syntax_Syntax.result_typ  in
                  let uu____58138 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____58138
                  then
                    let uu____58145 = patterns q  in
                    match uu____58145 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____58208 =
                       let uu____58209 =
                         let uu____58214 =
                           let uu____58215 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____58226 =
                             let uu____58237 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____58237]  in
                           uu____58215 :: uu____58226  in
                         (FStar_Parser_Const.imp_lid, uu____58214)  in
                       BaseConn uu____58209  in
                     FStar_Pervasives_Native.Some uu____58208))
           | uu____58270 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____58278 = un_squash t  in
      FStar_Util.bind_opt uu____58278
        (fun t1  ->
           let uu____58309 = head_and_args' t1  in
           match uu____58309 with
           | (hd1,args) ->
               let uu____58348 =
                 let uu____58363 =
                   let uu____58364 = un_uinst hd1  in
                   uu____58364.FStar_Syntax_Syntax.n  in
                 (uu____58363, args)  in
               (match uu____58348 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____58381)::(a2,uu____58383)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____58434 =
                      let uu____58435 = FStar_Syntax_Subst.compress a2  in
                      uu____58435.FStar_Syntax_Syntax.n  in
                    (match uu____58434 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____58442) ->
                         let uu____58477 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____58477 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____58530 -> failwith "impossible"  in
                              let uu____58538 = patterns q1  in
                              (match uu____58538 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____58599 -> FStar_Pervasives_Native.None)
                | uu____58600 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____58623 = destruct_sq_forall phi  in
          (match uu____58623 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58633  -> FStar_Pervasives_Native.Some _58633)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58640 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____58646 = destruct_sq_exists phi  in
          (match uu____58646 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58656  -> FStar_Pervasives_Native.Some _58656)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58663 -> f1)
      | uu____58666 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____58670 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____58670
      (fun uu____58675  ->
         let uu____58676 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____58676
           (fun uu____58681  ->
              let uu____58682 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____58682
                (fun uu____58687  ->
                   let uu____58688 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____58688
                     (fun uu____58693  ->
                        let uu____58694 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____58694
                          (fun uu____58698  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____58711 =
      let uu____58712 = FStar_Syntax_Subst.compress t  in
      uu____58712.FStar_Syntax_Syntax.n  in
    match uu____58711 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____58719) ->
        let uu____58754 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____58754 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____58788 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____58788
             then
               let uu____58795 =
                 let uu____58806 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____58806]  in
               mk_app t uu____58795
             else e1)
    | uu____58833 ->
        let uu____58834 =
          let uu____58845 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____58845]  in
        mk_app t uu____58834
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____58887 =
            let uu____58892 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____58892  in
          let uu____58893 =
            let uu____58894 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____58894  in
          let uu____58897 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____58887 a.FStar_Syntax_Syntax.action_univs uu____58893
            FStar_Parser_Const.effect_Tot_lid uu____58897 [] pos
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
    let uu____58923 =
      let uu____58930 =
        let uu____58931 =
          let uu____58948 =
            let uu____58959 = FStar_Syntax_Syntax.as_arg t  in [uu____58959]
             in
          (reify_1, uu____58948)  in
        FStar_Syntax_Syntax.Tm_app uu____58931  in
      FStar_Syntax_Syntax.mk uu____58930  in
    uu____58923 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____59014 =
        let uu____59021 =
          let uu____59022 =
            let uu____59023 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____59023  in
          FStar_Syntax_Syntax.Tm_constant uu____59022  in
        FStar_Syntax_Syntax.mk uu____59021  in
      uu____59014 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____59028 =
      let uu____59035 =
        let uu____59036 =
          let uu____59053 =
            let uu____59064 = FStar_Syntax_Syntax.as_arg t  in [uu____59064]
             in
          (reflect_, uu____59053)  in
        FStar_Syntax_Syntax.Tm_app uu____59036  in
      FStar_Syntax_Syntax.mk uu____59035  in
    uu____59028 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____59111 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____59136 = unfold_lazy i  in delta_qualifier uu____59136
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____59138 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____59139 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____59140 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____59163 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____59176 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____59177 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____59184 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____59185 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____59201) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____59206;
           FStar_Syntax_Syntax.index = uu____59207;
           FStar_Syntax_Syntax.sort = t2;_},uu____59209)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____59218) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____59224,uu____59225) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____59267) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____59292,t2,uu____59294) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____59319,t2) -> delta_qualifier t2
  
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
    let uu____59358 = delta_qualifier t  in incr_delta_depth uu____59358
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____59366 =
      let uu____59367 = FStar_Syntax_Subst.compress t  in
      uu____59367.FStar_Syntax_Syntax.n  in
    match uu____59366 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____59372 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____59388 =
      let uu____59405 = unmeta e  in head_and_args uu____59405  in
    match uu____59388 with
    | (head1,args) ->
        let uu____59436 =
          let uu____59451 =
            let uu____59452 = un_uinst head1  in
            uu____59452.FStar_Syntax_Syntax.n  in
          (uu____59451, args)  in
        (match uu____59436 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____59470) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____59494::(hd1,uu____59496)::(tl1,uu____59498)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____59565 =
               let uu____59568 =
                 let uu____59571 = list_elements tl1  in
                 FStar_Util.must uu____59571  in
               hd1 :: uu____59568  in
             FStar_Pervasives_Native.Some uu____59565
         | uu____59580 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____59604 .
    ('Auu____59604 -> 'Auu____59604) ->
      'Auu____59604 Prims.list -> 'Auu____59604 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____59630 = f a  in [uu____59630]
      | x::xs -> let uu____59635 = apply_last f xs  in x :: uu____59635
  
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
          let uu____59690 =
            let uu____59697 =
              let uu____59698 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____59698  in
            FStar_Syntax_Syntax.mk uu____59697  in
          uu____59690 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____59715 =
            let uu____59720 =
              let uu____59721 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59721
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59720 args  in
          uu____59715 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____59737 =
            let uu____59742 =
              let uu____59743 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59743
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59742 args  in
          uu____59737 FStar_Pervasives_Native.None pos  in
        let uu____59746 =
          let uu____59747 =
            let uu____59748 = FStar_Syntax_Syntax.iarg typ  in [uu____59748]
             in
          nil uu____59747 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____59782 =
                 let uu____59783 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____59792 =
                   let uu____59803 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____59812 =
                     let uu____59823 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____59823]  in
                   uu____59803 :: uu____59812  in
                 uu____59783 :: uu____59792  in
               cons1 uu____59782 t.FStar_Syntax_Syntax.pos) l uu____59746
  
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
        | uu____59932 -> false
  
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
          | uu____60046 -> false
  
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
        | uu____60212 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____60261 = FStar_ST.op_Bang debug_term_eq  in
          if uu____60261
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
        let t11 = let uu____60483 = unmeta_safe t1  in canon_app uu____60483
           in
        let t21 = let uu____60489 = unmeta_safe t2  in canon_app uu____60489
           in
        let uu____60492 =
          let uu____60497 =
            let uu____60498 =
              let uu____60501 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____60501  in
            uu____60498.FStar_Syntax_Syntax.n  in
          let uu____60502 =
            let uu____60503 =
              let uu____60506 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____60506  in
            uu____60503.FStar_Syntax_Syntax.n  in
          (uu____60497, uu____60502)  in
        match uu____60492 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____60508,uu____60509) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60518,FStar_Syntax_Syntax.Tm_uinst uu____60519) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____60528,uu____60529) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60554,FStar_Syntax_Syntax.Tm_delayed uu____60555) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____60580,uu____60581) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60610,FStar_Syntax_Syntax.Tm_ascribed uu____60611) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____60650 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____60650
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____60655 = FStar_Const.eq_const c1 c2  in
            check "const" uu____60655
        | (FStar_Syntax_Syntax.Tm_type
           uu____60658,FStar_Syntax_Syntax.Tm_type uu____60659) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____60717 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____60717) &&
              (let uu____60727 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____60727)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____60776 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____60776) &&
              (let uu____60786 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____60786)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____60804 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____60804)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____60861 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____60861) &&
              (let uu____60865 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____60865)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____60954 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____60954) &&
              (let uu____60958 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____60958)
        | (FStar_Syntax_Syntax.Tm_lazy uu____60975,uu____60976) ->
            let uu____60977 =
              let uu____60979 = unlazy t11  in
              term_eq_dbg dbg uu____60979 t21  in
            check "lazy_l" uu____60977
        | (uu____60981,FStar_Syntax_Syntax.Tm_lazy uu____60982) ->
            let uu____60983 =
              let uu____60985 = unlazy t21  in
              term_eq_dbg dbg t11 uu____60985  in
            check "lazy_r" uu____60983
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____61030 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____61030))
              &&
              (let uu____61034 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____61034)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____61038),FStar_Syntax_Syntax.Tm_uvar (u2,uu____61040)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____61098 =
               let uu____61100 = eq_quoteinfo qi1 qi2  in uu____61100 = Equal
                in
             check "tm_quoted qi" uu____61098) &&
              (let uu____61103 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____61103)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____61133 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____61133) &&
                   (let uu____61137 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____61137)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____61156 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____61156) &&
                    (let uu____61160 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____61160))
                   &&
                   (let uu____61164 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____61164)
             | uu____61167 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____61173) -> fail "unk"
        | (uu____61175,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____61177,uu____61178) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____61180,uu____61181) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____61183,uu____61184) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____61186,uu____61187) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____61189,uu____61190) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____61192,uu____61193) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____61213,uu____61214) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____61230,uu____61231) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____61239,uu____61240) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____61258,uu____61259) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____61283,uu____61284) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____61299,uu____61300) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____61314,uu____61315) ->
            fail "bottom"
        | (uu____61323,FStar_Syntax_Syntax.Tm_bvar uu____61324) ->
            fail "bottom"
        | (uu____61326,FStar_Syntax_Syntax.Tm_name uu____61327) ->
            fail "bottom"
        | (uu____61329,FStar_Syntax_Syntax.Tm_fvar uu____61330) ->
            fail "bottom"
        | (uu____61332,FStar_Syntax_Syntax.Tm_constant uu____61333) ->
            fail "bottom"
        | (uu____61335,FStar_Syntax_Syntax.Tm_type uu____61336) ->
            fail "bottom"
        | (uu____61338,FStar_Syntax_Syntax.Tm_abs uu____61339) ->
            fail "bottom"
        | (uu____61359,FStar_Syntax_Syntax.Tm_arrow uu____61360) ->
            fail "bottom"
        | (uu____61376,FStar_Syntax_Syntax.Tm_refine uu____61377) ->
            fail "bottom"
        | (uu____61385,FStar_Syntax_Syntax.Tm_app uu____61386) ->
            fail "bottom"
        | (uu____61404,FStar_Syntax_Syntax.Tm_match uu____61405) ->
            fail "bottom"
        | (uu____61429,FStar_Syntax_Syntax.Tm_let uu____61430) ->
            fail "bottom"
        | (uu____61445,FStar_Syntax_Syntax.Tm_uvar uu____61446) ->
            fail "bottom"
        | (uu____61460,FStar_Syntax_Syntax.Tm_meta uu____61461) ->
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
               let uu____61496 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____61496)
          (fun q1  ->
             fun q2  ->
               let uu____61508 =
                 let uu____61510 = eq_aqual q1 q2  in uu____61510 = Equal  in
               check "arg qual" uu____61508) a1 a2

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
               let uu____61535 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____61535)
          (fun q1  ->
             fun q2  ->
               let uu____61547 =
                 let uu____61549 = eq_aqual q1 q2  in uu____61549 = Equal  in
               check "binder qual" uu____61547) b1 b2

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
        ((let uu____61569 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____61569) &&
           (let uu____61573 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____61573))
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
    fun uu____61583  ->
      fun uu____61584  ->
        match (uu____61583, uu____61584) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____61711 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____61711) &&
               (let uu____61715 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____61715))
              &&
              (let uu____61719 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____61761 -> false  in
               check "branch when" uu____61719)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____61782 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____61782) &&
           (let uu____61791 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____61791))
          &&
          (let uu____61795 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____61795)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____61812 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____61812 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____61866 ->
        let uu____61889 =
          let uu____61891 = FStar_Syntax_Subst.compress t  in
          sizeof uu____61891  in
        (Prims.parse_int "1") + uu____61889
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____61894 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61894
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____61898 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61898
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____61907 = sizeof t1  in (FStar_List.length us) + uu____61907
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____61911) ->
        let uu____61936 = sizeof t1  in
        let uu____61938 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____61953  ->
                 match uu____61953 with
                 | (bv,uu____61963) ->
                     let uu____61968 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____61968) (Prims.parse_int "0") bs
           in
        uu____61936 + uu____61938
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____61997 = sizeof hd1  in
        let uu____61999 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____62014  ->
                 match uu____62014 with
                 | (arg,uu____62024) ->
                     let uu____62029 = sizeof arg  in acc + uu____62029)
            (Prims.parse_int "0") args
           in
        uu____61997 + uu____61999
    | uu____62032 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____62046 =
        let uu____62047 = un_uinst t  in uu____62047.FStar_Syntax_Syntax.n
         in
      match uu____62046 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____62052 -> false
  
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
        let uu____62101 = FStar_Options.set_options t s  in
        match uu____62101 with
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
          ((let uu____62118 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____62118 (fun a1  -> ()));
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
          let uu____62133 = FStar_Options.internal_pop ()  in
          if uu____62133
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
    | FStar_Syntax_Syntax.Tm_delayed uu____62165 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____62192 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____62207 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____62208 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____62209 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____62218) ->
        let uu____62243 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____62243 with
         | (bs1,t2) ->
             let uu____62252 =
               FStar_List.collect
                 (fun uu____62264  ->
                    match uu____62264 with
                    | (b,uu____62274) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62279 = unbound_variables t2  in
             FStar_List.append uu____62252 uu____62279)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____62304 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____62304 with
         | (bs1,c1) ->
             let uu____62313 =
               FStar_List.collect
                 (fun uu____62325  ->
                    match uu____62325 with
                    | (b,uu____62335) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62340 = unbound_variables_comp c1  in
             FStar_List.append uu____62313 uu____62340)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____62349 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____62349 with
         | (bs,t2) ->
             let uu____62372 =
               FStar_List.collect
                 (fun uu____62384  ->
                    match uu____62384 with
                    | (b1,uu____62394) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____62399 = unbound_variables t2  in
             FStar_List.append uu____62372 uu____62399)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____62428 =
          FStar_List.collect
            (fun uu____62442  ->
               match uu____62442 with
               | (x,uu____62454) -> unbound_variables x) args
           in
        let uu____62463 = unbound_variables t1  in
        FStar_List.append uu____62428 uu____62463
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____62504 = unbound_variables t1  in
        let uu____62507 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____62522 = FStar_Syntax_Subst.open_branch br  in
                  match uu____62522 with
                  | (p,wopt,t2) ->
                      let uu____62544 = unbound_variables t2  in
                      let uu____62547 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____62544 uu____62547))
           in
        FStar_List.append uu____62504 uu____62507
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____62561) ->
        let uu____62602 = unbound_variables t1  in
        let uu____62605 =
          let uu____62608 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____62639 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____62608 uu____62639  in
        FStar_List.append uu____62602 uu____62605
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____62680 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____62683 =
          let uu____62686 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____62689 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____62694 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____62696 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____62696 with
                 | (uu____62717,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____62686 uu____62689  in
        FStar_List.append uu____62680 uu____62683
    | FStar_Syntax_Syntax.Tm_let ((uu____62719,lbs),t1) ->
        let uu____62739 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____62739 with
         | (lbs1,t2) ->
             let uu____62754 = unbound_variables t2  in
             let uu____62757 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____62764 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____62767 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____62764 uu____62767) lbs1
                in
             FStar_List.append uu____62754 uu____62757)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____62784 = unbound_variables t1  in
        let uu____62787 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____62826  ->
                      match uu____62826 with
                      | (a,uu____62838) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____62847,uu____62848,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____62854,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____62860 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____62869 -> []
          | FStar_Syntax_Syntax.Meta_named uu____62870 -> []  in
        FStar_List.append uu____62784 uu____62787

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____62877) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____62887) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____62897 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____62900 =
          FStar_List.collect
            (fun uu____62914  ->
               match uu____62914 with
               | (a,uu____62926) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____62897 uu____62900

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
            let uu____63041 = head_and_args h  in
            (match uu____63041 with
             | (head1,args) ->
                 let uu____63102 =
                   let uu____63103 = FStar_Syntax_Subst.compress head1  in
                   uu____63103.FStar_Syntax_Syntax.n  in
                 (match uu____63102 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____63156 -> aux (h :: acc) t))
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
      let uu____63180 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____63180 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2985_63222 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2985_63222.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2985_63222.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2985_63222.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2985_63222.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  