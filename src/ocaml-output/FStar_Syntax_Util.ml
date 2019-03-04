open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____44959 = FStar_ST.op_Bang tts_f  in
    match uu____44959 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____45023 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____45023 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____45030 =
      let uu____45033 =
        let uu____45036 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____45036]  in
      FStar_List.append lid.FStar_Ident.ns uu____45033  in
    FStar_Ident.lid_of_ids uu____45030
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____45054 .
    (FStar_Syntax_Syntax.bv * 'Auu____45054) ->
      (FStar_Syntax_Syntax.term * 'Auu____45054)
  =
  fun uu____45067  ->
    match uu____45067 with
    | (b,imp) ->
        let uu____45074 = FStar_Syntax_Syntax.bv_to_name b  in
        (uu____45074, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____45126 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____45126
            then []
            else
              (let uu____45145 = arg_of_non_null_binder b  in [uu____45145])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____45180 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____45262 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45262
              then
                let b1 =
                  let uu____45288 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____45288, (FStar_Pervasives_Native.snd b))  in
                let uu____45295 = arg_of_non_null_binder b1  in
                (b1, uu____45295)
              else
                (let uu____45318 = arg_of_non_null_binder b  in
                 (b, uu____45318))))
       in
    FStar_All.pipe_right uu____45180 FStar_List.unzip
  
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
              let uu____45452 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45452
              then
                let uu____45461 = b  in
                match uu____45461 with
                | (a,imp) ->
                    let b1 =
                      let uu____45481 =
                        let uu____45483 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____45483  in
                      FStar_Ident.id_of_text uu____45481  in
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
        let uu____45528 =
          let uu____45535 =
            let uu____45536 =
              let uu____45551 = name_binders binders  in (uu____45551, comp)
               in
            FStar_Syntax_Syntax.Tm_arrow uu____45536  in
          FStar_Syntax_Syntax.mk uu____45535  in
        uu____45528 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____45573 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45610  ->
            match uu____45610 with
            | (t,imp) ->
                let uu____45621 =
                  let uu____45622 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____45622
                   in
                (uu____45621, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45677  ->
            match uu____45677 with
            | (t,imp) ->
                let uu____45694 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____45694, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____45707 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____45707
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____45719 . 'Auu____45719 -> 'Auu____45719 Prims.list =
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
          (fun uu____45845  ->
             fun uu____45846  ->
               match (uu____45845, uu____45846) with
               | ((x,uu____45872),(y,uu____45874)) ->
                   let uu____45895 =
                     let uu____45902 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____45902)  in
                   FStar_Syntax_Syntax.NT uu____45895) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____45918) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45924,uu____45925) ->
        unmeta e2
    | uu____45966 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____45980 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____45987 -> e1
         | uu____45996 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45998,uu____45999) ->
        unmeta_safe e2
    | uu____46040 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____46059 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____46062 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____46076 = univ_kernel u1  in
        (match uu____46076 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____46093 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____46102 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____46117 = univ_kernel u  in
    FStar_Pervasives_Native.snd uu____46117
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____46137,uu____46138) ->
          failwith "Impossible: compare_univs"
      | (uu____46142,FStar_Syntax_Syntax.U_bvar uu____46143) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____46148) ->
          ~- (Prims.parse_int "1")
      | (uu____46150,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____46153) -> ~- (Prims.parse_int "1")
      | (uu____46155,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____46159,FStar_Syntax_Syntax.U_unif
         uu____46160) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____46170,FStar_Syntax_Syntax.U_name
         uu____46171) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____46199 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____46201 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____46199 - uu____46201
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____46237 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____46237
                 (fun uu____46253  ->
                    match uu____46253 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____46281,uu____46282) ->
          ~- (Prims.parse_int "1")
      | (uu____46286,FStar_Syntax_Syntax.U_max uu____46287) ->
          (Prims.parse_int "1")
      | uu____46291 ->
          let uu____46296 = univ_kernel u1  in
          (match uu____46296 with
           | (k1,n1) ->
               let uu____46307 = univ_kernel u2  in
               (match uu____46307 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____46338 = compare_univs u1 u2  in
      uu____46338 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____46357 =
        let uu____46358 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____46358;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____46357
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____46378 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____46387 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____46410 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____46419 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____46446 =
          let uu____46447 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46447  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46446;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____46476 =
          let uu____46477 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46477  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46476;
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
      let uu___631_46513 = c  in
      let uu____46514 =
        let uu____46515 =
          let uu___633_46516 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___633_46516.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___633_46516.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___633_46516.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___633_46516.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____46515  in
      {
        FStar_Syntax_Syntax.n = uu____46514;
        FStar_Syntax_Syntax.pos = (uu___631_46513.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___631_46513.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____46542 -> c
        | FStar_Syntax_Syntax.GTotal uu____46551 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___645_46562 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___645_46562.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___645_46562.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___645_46562.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___645_46562.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___648_46563 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___648_46563.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___648_46563.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____46566  ->
           let uu____46567 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____46567)
  
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
    | uu____46607 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____46622 -> true
    | FStar_Syntax_Syntax.GTotal uu____46632 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___402_46657  ->
               match uu___402_46657 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46661 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___403_46674  ->
               match uu___403_46674 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46678 -> false)))
  
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
            (fun uu___404_46691  ->
               match uu___404_46691 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46695 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___405_46712  ->
            match uu___405_46712 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46716 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___406_46729  ->
            match uu___406_46729 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46733 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____46765 -> true
    | FStar_Syntax_Syntax.GTotal uu____46775 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___407_46790  ->
                   match uu___407_46790 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____46793 -> false)))
  
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
            (fun uu___408_46838  ->
               match uu___408_46838 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____46841 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46857 =
      let uu____46858 = FStar_Syntax_Subst.compress t  in
      uu____46858.FStar_Syntax_Syntax.n  in
    match uu____46857 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46862,c) -> is_pure_or_ghost_comp c
    | uu____46884 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____46899 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46908 =
      let uu____46909 = FStar_Syntax_Subst.compress t  in
      uu____46909.FStar_Syntax_Syntax.n  in
    match uu____46908 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46913,c) -> is_lemma_comp c
    | uu____46935 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____46943 =
      let uu____46944 = FStar_Syntax_Subst.compress t  in
      uu____46944.FStar_Syntax_Syntax.n  in
    match uu____46943 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____46948) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____46974) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____47011,t1,uu____47013) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____47039,uu____47040) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____47082) -> head_of t1
    | uu____47087 -> t
  
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
    | uu____47165 -> (t1, [])
  
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
        let uu____47247 = head_and_args' head1  in
        (match uu____47247 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____47316 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____47343) ->
        FStar_Syntax_Subst.compress t2
    | uu____47348 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____47356 =
      let uu____47357 = FStar_Syntax_Subst.compress t  in
      uu____47357.FStar_Syntax_Syntax.n  in
    match uu____47356 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____47361,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____47389)::uu____47390 ->
                  let pats' = unmeta pats  in
                  let uu____47450 = head_and_args pats'  in
                  (match uu____47450 with
                   | (head1,uu____47469) ->
                       let uu____47494 =
                         let uu____47495 = un_uinst head1  in
                         uu____47495.FStar_Syntax_Syntax.n  in
                       (match uu____47494 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____47500 -> false))
              | uu____47502 -> false)
         | uu____47514 -> false)
    | uu____47516 -> false
  
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
                (fun uu___409_47535  ->
                   match uu___409_47535 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____47538 -> false)))
    | uu____47540 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____47557) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____47567) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____47596 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____47605 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___827_47617 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___827_47617.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___827_47617.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___827_47617.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___827_47617.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____47631  ->
           let uu____47632 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____47632 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___410_47650  ->
            match uu___410_47650 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____47654 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____47662 -> []
    | FStar_Syntax_Syntax.GTotal uu____47679 -> []
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
    | uu____47723 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____47733,uu____47734) ->
        unascribe e2
    | uu____47775 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____47828,uu____47829) ->
          ascribe t' k
      | uu____47870 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____47897 =
      let uu____47906 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____47906  in
    uu____47897 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47962 =
      let uu____47963 = FStar_Syntax_Subst.compress t  in
      uu____47963.FStar_Syntax_Syntax.n  in
    match uu____47962 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____47967 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____47967
    | uu____47968 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47975 =
      let uu____47976 = FStar_Syntax_Subst.compress t  in
      uu____47976.FStar_Syntax_Syntax.n  in
    match uu____47975 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____47980 ->
             let uu____47989 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____47989
         | uu____47990 -> t)
    | uu____47991 -> t
  
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
      | uu____48015 -> false
  
let rec unlazy_as_t :
  'Auu____48028 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_Syntax_Syntax.term -> 'Auu____48028
  =
  fun k  ->
    fun t  ->
      let uu____48039 =
        let uu____48040 = FStar_Syntax_Subst.compress t  in
        uu____48040.FStar_Syntax_Syntax.n  in
      match uu____48039 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____48045;
            FStar_Syntax_Syntax.rng = uu____48046;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____48049 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____48090 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____48090;
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
    let uu____48103 =
      let uu____48118 = unascribe t  in head_and_args' uu____48118  in
    match uu____48103 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____48152 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____48163 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____48174 -> false
  
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
      | (NotEqual ,uu____48224) -> NotEqual
      | (uu____48225,NotEqual ) -> NotEqual
      | (Unknown ,uu____48226) -> Unknown
      | (uu____48227,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___411_48348 = if uu___411_48348 then Equal else Unknown
         in
      let equal_iff uu___412_48359 =
        if uu___412_48359 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____48380 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____48402 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____48402
        then
          let uu____48406 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____48483  ->
                    match uu____48483 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____48524 = eq_tm a1 a2  in
                        eq_inj acc uu____48524) Equal) uu____48406
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____48538 =
          let uu____48555 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____48555 head_and_args  in
        match uu____48538 with
        | (head1,args1) ->
            let uu____48608 =
              let uu____48625 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____48625 head_and_args  in
            (match uu____48608 with
             | (head2,args2) ->
                 let uu____48678 =
                   let uu____48683 =
                     let uu____48684 = un_uinst head1  in
                     uu____48684.FStar_Syntax_Syntax.n  in
                   let uu____48687 =
                     let uu____48688 = un_uinst head2  in
                     uu____48688.FStar_Syntax_Syntax.n  in
                   (uu____48683, uu____48687)  in
                 (match uu____48678 with
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
                  | uu____48715 -> FStar_Pervasives_Native.None))
         in
      let uu____48728 =
        let uu____48733 =
          let uu____48734 = unmeta t11  in uu____48734.FStar_Syntax_Syntax.n
           in
        let uu____48737 =
          let uu____48738 = unmeta t21  in uu____48738.FStar_Syntax_Syntax.n
           in
        (uu____48733, uu____48737)  in
      match uu____48728 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____48744,uu____48745) ->
          let uu____48746 = unlazy t11  in eq_tm uu____48746 t21
      | (uu____48747,FStar_Syntax_Syntax.Tm_lazy uu____48748) ->
          let uu____48749 = unlazy t21  in eq_tm t11 uu____48749
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____48752 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____48776 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____48776
            (fun uu____48824  ->
               match uu____48824 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____48839 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____48839
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____48853 = eq_tm f g  in
          eq_and uu____48853
            (fun uu____48856  ->
               let uu____48857 = eq_univs_list us vs  in equal_if uu____48857)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48859),uu____48860) -> Unknown
      | (uu____48861,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48862)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____48865 = FStar_Const.eq_const c d  in
          equal_iff uu____48865
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____48868)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____48870))) ->
          let uu____48899 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____48899
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____48953 =
            let uu____48958 =
              let uu____48959 = un_uinst h1  in
              uu____48959.FStar_Syntax_Syntax.n  in
            let uu____48962 =
              let uu____48963 = un_uinst h2  in
              uu____48963.FStar_Syntax_Syntax.n  in
            (uu____48958, uu____48962)  in
          (match uu____48953 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____48969 =
                    let uu____48971 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____48971  in
                  FStar_List.mem uu____48969 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____48973 ->
               let uu____48978 = eq_tm h1 h2  in
               eq_and uu____48978 (fun uu____48980  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____49086 = FStar_List.zip bs1 bs2  in
            let uu____49149 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____49186  ->
                 fun a  ->
                   match uu____49186 with
                   | (b1,b2) ->
                       eq_and a (fun uu____49279  -> branch_matches b1 b2))
              uu____49086 uu____49149
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____49284 = eq_univs u v1  in equal_if uu____49284
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____49298 = eq_quoteinfo q1 q2  in
          eq_and uu____49298 (fun uu____49300  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____49313 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____49313 (fun uu____49315  -> eq_tm phi1 phi2)
      | uu____49316 -> Unknown

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
      | ([],uu____49388) -> NotEqual
      | (uu____49419,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____49511 = eq_tm t1 t2  in
             match uu____49511 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____49512 = eq_antiquotes a11 a21  in
                 (match uu____49512 with
                  | NotEqual  -> NotEqual
                  | uu____49513 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____49528) -> NotEqual
      | (uu____49535,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____49565 -> NotEqual

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
        | (uu____49657,uu____49658) -> false  in
      let uu____49668 = b1  in
      match uu____49668 with
      | (p1,w1,t1) ->
          let uu____49702 = b2  in
          (match uu____49702 with
           | (p2,w2,t2) ->
               let uu____49736 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____49736
               then
                 let uu____49739 =
                   (let uu____49743 = eq_tm t1 t2  in uu____49743 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____49752 = eq_tm t11 t21  in
                             uu____49752 = Equal) w1 w2)
                    in
                 (if uu____49739 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____49817)::a11,(b,uu____49820)::b1) ->
          let uu____49894 = eq_tm a b  in
          (match uu____49894 with
           | Equal  -> eq_args a11 b1
           | uu____49895 -> Unknown)
      | uu____49896 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____49932) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____49938,uu____49939) ->
        unrefine t2
    | uu____49980 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____49988 =
      let uu____49989 = FStar_Syntax_Subst.compress t  in
      uu____49989.FStar_Syntax_Syntax.n  in
    match uu____49988 with
    | FStar_Syntax_Syntax.Tm_uvar uu____49993 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50008) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____50013 ->
        let uu____50030 =
          let uu____50031 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____50031 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____50030 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____50094,uu____50095) ->
        is_uvar t1
    | uu____50136 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50145 =
      let uu____50146 = unrefine t  in uu____50146.FStar_Syntax_Syntax.n  in
    match uu____50145 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50152) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50178) -> is_unit t1
    | uu____50183 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50192 =
      let uu____50193 = FStar_Syntax_Subst.compress t  in
      uu____50193.FStar_Syntax_Syntax.n  in
    match uu____50192 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____50198 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50207 =
      let uu____50208 = unrefine t  in uu____50208.FStar_Syntax_Syntax.n  in
    match uu____50207 with
    | FStar_Syntax_Syntax.Tm_type uu____50212 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50216) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50242) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____50247,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____50269 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____50278 =
      let uu____50279 = FStar_Syntax_Subst.compress e  in
      uu____50279.FStar_Syntax_Syntax.n  in
    match uu____50278 with
    | FStar_Syntax_Syntax.Tm_abs uu____50283 -> true
    | uu____50303 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50312 =
      let uu____50313 = FStar_Syntax_Subst.compress t  in
      uu____50313.FStar_Syntax_Syntax.n  in
    match uu____50312 with
    | FStar_Syntax_Syntax.Tm_arrow uu____50317 -> true
    | uu____50333 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____50343) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____50349,uu____50350) ->
        pre_typ t2
    | uu____50391 -> t1
  
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
      let uu____50416 =
        let uu____50417 = un_uinst typ1  in uu____50417.FStar_Syntax_Syntax.n
         in
      match uu____50416 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____50482 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____50512 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____50533,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____50540) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____50545,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____50556,uu____50557,uu____50558,uu____50559,uu____50560) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____50570,uu____50571,uu____50572,uu____50573) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____50579,uu____50580,uu____50581,uu____50582,uu____50583) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____50591,uu____50592) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____50594,uu____50595) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____50598 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____50599 -> []
    | FStar_Syntax_Syntax.Sig_main uu____50600 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____50614 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___413_50640  ->
    match uu___413_50640 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____50654 'Auu____50655 .
    ('Auu____50654 FStar_Syntax_Syntax.syntax * 'Auu____50655) ->
      FStar_Range.range
  =
  fun uu____50666  ->
    match uu____50666 with | (hd1,uu____50674) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____50688 'Auu____50689 .
    ('Auu____50688 FStar_Syntax_Syntax.syntax * 'Auu____50689) Prims.list ->
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
      | uu____50787 ->
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
      let uu____50846 =
        FStar_List.map
          (fun uu____50873  ->
             match uu____50873 with
             | (bv,aq) ->
                 let uu____50892 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____50892, aq)) bs
         in
      mk_app f uu____50846
  
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
          let uu____50942 = FStar_Ident.range_of_lid l  in
          let uu____50943 =
            let uu____50952 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____50952  in
          uu____50943 FStar_Pervasives_Native.None uu____50942
      | uu____50960 ->
          let e =
            let uu____50974 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____50974 args  in
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
          let uu____51051 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____51051
          then
            let uu____51054 =
              let uu____51060 =
                let uu____51062 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____51062  in
              let uu____51065 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____51060, uu____51065)  in
            FStar_Ident.mk_ident uu____51054
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___1421_51070 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___1421_51070.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___1421_51070.FStar_Syntax_Syntax.sort)
          }  in
        let uu____51071 = mk_field_projector_name_from_ident lid nm  in
        (uu____51071, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____51083) -> ses
    | uu____51092 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____51103 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____51116 = FStar_Syntax_Unionfind.find uv  in
      match uu____51116 with
      | FStar_Pervasives_Native.Some uu____51119 ->
          let uu____51120 =
            let uu____51122 =
              let uu____51124 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____51124  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____51122  in
          failwith uu____51120
      | uu____51129 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____51212 -> q1 = q2
  
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
              let uu____51258 =
                let uu___1482_51259 = rc  in
                let uu____51260 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1482_51259.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____51260;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1482_51259.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____51258
           in
        match bs with
        | [] -> t
        | uu____51277 ->
            let body =
              let uu____51279 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____51279  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____51309 =
                   let uu____51316 =
                     let uu____51317 =
                       let uu____51336 =
                         let uu____51345 =
                           FStar_Syntax_Subst.close_binders bs  in
                         FStar_List.append uu____51345 bs'  in
                       let uu____51360 = close_lopt lopt'  in
                       (uu____51336, t1, uu____51360)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51317  in
                   FStar_Syntax_Syntax.mk uu____51316  in
                 uu____51309 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____51378 ->
                 let uu____51379 =
                   let uu____51386 =
                     let uu____51387 =
                       let uu____51406 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____51415 = close_lopt lopt  in
                       (uu____51406, body, uu____51415)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51387  in
                   FStar_Syntax_Syntax.mk uu____51386  in
                 uu____51379 FStar_Pervasives_Native.None
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
      | uu____51474 ->
          let uu____51483 =
            let uu____51490 =
              let uu____51491 =
                let uu____51506 = FStar_Syntax_Subst.close_binders bs  in
                let uu____51515 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____51506, uu____51515)  in
              FStar_Syntax_Syntax.Tm_arrow uu____51491  in
            FStar_Syntax_Syntax.mk uu____51490  in
          uu____51483 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____51567 =
        let uu____51568 = FStar_Syntax_Subst.compress t  in
        uu____51568.FStar_Syntax_Syntax.n  in
      match uu____51567 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____51598) ->
               let uu____51607 =
                 let uu____51608 = FStar_Syntax_Subst.compress tres  in
                 uu____51608.FStar_Syntax_Syntax.n  in
               (match uu____51607 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____51651 -> t)
           | uu____51652 -> t)
      | uu____51653 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____51671 =
        let uu____51672 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____51672 t.FStar_Syntax_Syntax.pos  in
      let uu____51673 =
        let uu____51680 =
          let uu____51681 =
            let uu____51688 =
              let uu____51691 =
                let uu____51692 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____51692]  in
              FStar_Syntax_Subst.close uu____51691 t  in
            (b, uu____51688)  in
          FStar_Syntax_Syntax.Tm_refine uu____51681  in
        FStar_Syntax_Syntax.mk uu____51680  in
      uu____51673 FStar_Pervasives_Native.None uu____51671
  
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
        let uu____51775 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____51775 with
         | (bs1,c1) ->
             let uu____51794 = is_total_comp c1  in
             if uu____51794
             then
               let uu____51809 = arrow_formals_comp (comp_result c1)  in
               (match uu____51809 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____51876;
           FStar_Syntax_Syntax.index = uu____51877;
           FStar_Syntax_Syntax.sort = s;_},uu____51879)
        ->
        let rec aux s1 k2 =
          let uu____51910 =
            let uu____51911 = FStar_Syntax_Subst.compress s1  in
            uu____51911.FStar_Syntax_Syntax.n  in
          match uu____51910 with
          | FStar_Syntax_Syntax.Tm_arrow uu____51926 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____51941;
                 FStar_Syntax_Syntax.index = uu____51942;
                 FStar_Syntax_Syntax.sort = s2;_},uu____51944)
              -> aux s2 k2
          | uu____51952 ->
              let uu____51953 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____51953)
           in
        aux s k1
    | uu____51968 ->
        let uu____51969 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____51969)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____52004 = arrow_formals_comp k  in
    match uu____52004 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____52146 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____52146 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____52170 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___414_52179  ->
                         match uu___414_52179 with
                         | FStar_Syntax_Syntax.DECREASES uu____52181 -> true
                         | uu____52185 -> false))
                  in
               (match uu____52170 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____52220 ->
                    let uu____52223 = is_total_comp c1  in
                    if uu____52223
                    then
                      let uu____52242 =
                        arrow_until_decreases (comp_result c1)  in
                      (match uu____52242 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____52335;
             FStar_Syntax_Syntax.index = uu____52336;
             FStar_Syntax_Syntax.sort = k2;_},uu____52338)
          -> arrow_until_decreases k2
      | uu____52346 -> ([], FStar_Pervasives_Native.None)  in
    let uu____52367 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____52367 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____52421 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____52442 =
                 FStar_Common.tabulate n_univs (fun uu____52452  -> false)
                  in
               let uu____52455 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____52480  ->
                         match uu____52480 with
                         | (x,uu____52489) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____52442 uu____52455)
           in
        ((n_univs + (FStar_List.length bs)), uu____52421)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____52551 =
            let uu___1604_52552 = rc  in
            let uu____52553 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1604_52552.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____52553;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1604_52552.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____52551
      | uu____52562 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____52596 =
        let uu____52597 =
          let uu____52600 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____52600  in
        uu____52597.FStar_Syntax_Syntax.n  in
      match uu____52596 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____52646 = aux t2 what  in
          (match uu____52646 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____52718 -> ([], t1, abs_body_lcomp)  in
    let uu____52735 = aux t FStar_Pervasives_Native.None  in
    match uu____52735 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____52783 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____52783 with
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
                    | (FStar_Pervasives_Native.None ,uu____52946) -> def
                    | (uu____52957,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____52969) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _52985  ->
                                  FStar_Syntax_Syntax.U_name _52985))
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
            let uu____53067 = FStar_Syntax_Subst.open_univ_vars_comp uvs c
               in
            (match uu____53067 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____53102 ->
            let t' = arrow binders c  in
            let uu____53114 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____53114 with
             | (uvs1,t'1) ->
                 let uu____53135 =
                   let uu____53136 = FStar_Syntax_Subst.compress t'1  in
                   uu____53136.FStar_Syntax_Syntax.n  in
                 (match uu____53135 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____53185 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____53210 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____53221 -> false
  
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
      let uu____53284 =
        let uu____53285 = pre_typ t  in uu____53285.FStar_Syntax_Syntax.n  in
      match uu____53284 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____53290 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____53304 =
        let uu____53305 = pre_typ t  in uu____53305.FStar_Syntax_Syntax.n  in
      match uu____53304 with
      | FStar_Syntax_Syntax.Tm_fvar uu____53309 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____53311) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____53337) ->
          is_constructed_typ t1 lid
      | uu____53342 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____53355 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____53356 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____53357 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____53359) -> get_tycon t2
    | uu____53384 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____53392 =
      let uu____53393 = un_uinst t  in uu____53393.FStar_Syntax_Syntax.n  in
    match uu____53392 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____53398 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____53412 =
        let uu____53416 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____53416  in
      match uu____53412 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____53448 -> false
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
  fun uu____53467  ->
    let u =
      let uu____53473 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _53490  -> FStar_Syntax_Syntax.U_unif _53490)
        uu____53473
       in
    let uu____53491 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____53491, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____53504 = eq_tm a a'  in
      match uu____53504 with | Equal  -> true | uu____53507 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____53512 =
    let uu____53519 =
      let uu____53520 =
        let uu____53521 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____53521
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____53520  in
    FStar_Syntax_Syntax.mk uu____53519  in
  uu____53512 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____53636 =
            let uu____53639 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____53640 =
              let uu____53647 =
                let uu____53648 =
                  let uu____53665 =
                    let uu____53676 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____53685 =
                      let uu____53696 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____53696]  in
                    uu____53676 :: uu____53685  in
                  (tand, uu____53665)  in
                FStar_Syntax_Syntax.Tm_app uu____53648  in
              FStar_Syntax_Syntax.mk uu____53647  in
            uu____53640 FStar_Pervasives_Native.None uu____53639  in
          FStar_Pervasives_Native.Some uu____53636
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____53776 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____53777 =
          let uu____53784 =
            let uu____53785 =
              let uu____53802 =
                let uu____53813 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____53822 =
                  let uu____53833 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____53833]  in
                uu____53813 :: uu____53822  in
              (op_t, uu____53802)  in
            FStar_Syntax_Syntax.Tm_app uu____53785  in
          FStar_Syntax_Syntax.mk uu____53784  in
        uu____53777 FStar_Pervasives_Native.None uu____53776
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____53893 =
      let uu____53900 =
        let uu____53901 =
          let uu____53918 =
            let uu____53929 = FStar_Syntax_Syntax.as_arg phi  in
            [uu____53929]  in
          (t_not, uu____53918)  in
        FStar_Syntax_Syntax.Tm_app uu____53901  in
      FStar_Syntax_Syntax.mk uu____53900  in
    uu____53893 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____54129 =
      let uu____54136 =
        let uu____54137 =
          let uu____54154 =
            let uu____54165 = FStar_Syntax_Syntax.as_arg e  in [uu____54165]
             in
          (b2t_v, uu____54154)  in
        FStar_Syntax_Syntax.Tm_app uu____54137  in
      FStar_Syntax_Syntax.mk uu____54136  in
    uu____54129 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____54212 =
      let uu____54213 = unmeta t  in uu____54213.FStar_Syntax_Syntax.n  in
    match uu____54212 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____54218 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54241 = is_t_true t1  in
      if uu____54241
      then t2
      else
        (let uu____54248 = is_t_true t2  in
         if uu____54248 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54276 = is_t_true t1  in
      if uu____54276
      then t_true
      else
        (let uu____54283 = is_t_true t2  in
         if uu____54283 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____54312 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____54313 =
        let uu____54320 =
          let uu____54321 =
            let uu____54338 =
              let uu____54349 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____54358 =
                let uu____54369 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____54369]  in
              uu____54349 :: uu____54358  in
            (teq, uu____54338)  in
          FStar_Syntax_Syntax.Tm_app uu____54321  in
        FStar_Syntax_Syntax.mk uu____54320  in
      uu____54313 FStar_Pervasives_Native.None uu____54312
  
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
          let uu____54439 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____54440 =
            let uu____54447 =
              let uu____54448 =
                let uu____54465 =
                  let uu____54476 = FStar_Syntax_Syntax.iarg t  in
                  let uu____54485 =
                    let uu____54496 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____54505 =
                      let uu____54516 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____54516]  in
                    uu____54496 :: uu____54505  in
                  uu____54476 :: uu____54485  in
                (eq_inst, uu____54465)  in
              FStar_Syntax_Syntax.Tm_app uu____54448  in
            FStar_Syntax_Syntax.mk uu____54447  in
          uu____54440 FStar_Pervasives_Native.None uu____54439
  
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
        let uu____54596 =
          let uu____54603 =
            let uu____54604 =
              let uu____54621 =
                let uu____54632 = FStar_Syntax_Syntax.iarg t  in
                let uu____54641 =
                  let uu____54652 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____54661 =
                    let uu____54672 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____54672]  in
                  uu____54652 :: uu____54661  in
                uu____54632 :: uu____54641  in
              (t_has_type1, uu____54621)  in
            FStar_Syntax_Syntax.Tm_app uu____54604  in
          FStar_Syntax_Syntax.mk uu____54603  in
        uu____54596 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____54752 =
          let uu____54759 =
            let uu____54760 =
              let uu____54777 =
                let uu____54788 = FStar_Syntax_Syntax.iarg t  in
                let uu____54797 =
                  let uu____54808 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____54808]  in
                uu____54788 :: uu____54797  in
              (t_with_type1, uu____54777)  in
            FStar_Syntax_Syntax.Tm_app uu____54760  in
          FStar_Syntax_Syntax.mk uu____54759  in
        uu____54752 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____54858 =
    let uu____54865 =
      let uu____54866 =
        let uu____54873 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____54873, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____54866  in
    FStar_Syntax_Syntax.mk uu____54865  in
  uu____54858 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____54891 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____54904 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____54915 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____54891 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____54936  -> c0)
  
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
        let uu____55019 =
          let uu____55026 =
            let uu____55027 =
              let uu____55044 =
                let uu____55055 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____55064 =
                  let uu____55075 =
                    let uu____55084 =
                      let uu____55085 =
                        let uu____55086 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____55086]  in
                      abs uu____55085 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____55084  in
                  [uu____55075]  in
                uu____55055 :: uu____55064  in
              (fa, uu____55044)  in
            FStar_Syntax_Syntax.Tm_app uu____55027  in
          FStar_Syntax_Syntax.mk uu____55026  in
        uu____55019 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____55216 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____55216
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____55235 -> true
    | uu____55237 -> false
  
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
          let uu____55284 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____55284, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____55313 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____55313, FStar_Pervasives_Native.None, t2)  in
        let uu____55327 =
          let uu____55328 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____55328  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____55327
  
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
      let uu____55404 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55407 =
        let uu____55418 = FStar_Syntax_Syntax.as_arg p  in [uu____55418]  in
      mk_app uu____55404 uu____55407
  
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
      let uu____55458 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55461 =
        let uu____55472 = FStar_Syntax_Syntax.as_arg p  in [uu____55472]  in
      mk_app uu____55458 uu____55461
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55507 = head_and_args t  in
    match uu____55507 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____55556 =
          let uu____55571 =
            let uu____55572 = FStar_Syntax_Subst.compress head3  in
            uu____55572.FStar_Syntax_Syntax.n  in
          (uu____55571, args)  in
        (match uu____55556 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____55591)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____55657 =
                    let uu____55662 =
                      let uu____55663 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____55663]  in
                    FStar_Syntax_Subst.open_term uu____55662 p  in
                  (match uu____55657 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____55720 -> failwith "impossible"  in
                       let uu____55728 =
                         let uu____55730 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____55730
                          in
                       if uu____55728
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____55746 -> FStar_Pervasives_Native.None)
         | uu____55749 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55780 = head_and_args t  in
    match uu____55780 with
    | (head1,args) ->
        let uu____55831 =
          let uu____55846 =
            let uu____55847 = FStar_Syntax_Subst.compress head1  in
            uu____55847.FStar_Syntax_Syntax.n  in
          (uu____55846, args)  in
        (match uu____55831 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____55869;
               FStar_Syntax_Syntax.vars = uu____55870;_},u::[]),(t1,uu____55873)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____55920 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55955 = head_and_args t  in
    match uu____55955 with
    | (head1,args) ->
        let uu____56006 =
          let uu____56021 =
            let uu____56022 = FStar_Syntax_Subst.compress head1  in
            uu____56022.FStar_Syntax_Syntax.n  in
          (uu____56021, args)  in
        (match uu____56006 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____56044;
               FStar_Syntax_Syntax.vars = uu____56045;_},u::[]),(t1,uu____56048)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____56095 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____56123 =
      let uu____56140 = unmeta t  in head_and_args uu____56140  in
    match uu____56123 with
    | (head1,uu____56143) ->
        let uu____56168 =
          let uu____56169 = un_uinst head1  in
          uu____56169.FStar_Syntax_Syntax.n  in
        (match uu____56168 with
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
         | uu____56174 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____56194 =
      let uu____56207 =
        let uu____56208 = FStar_Syntax_Subst.compress t  in
        uu____56208.FStar_Syntax_Syntax.n  in
      match uu____56207 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____56338 =
            let uu____56349 =
              let uu____56350 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____56350  in
            (b, uu____56349)  in
          FStar_Pervasives_Native.Some uu____56338
      | uu____56367 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____56194
      (fun uu____56405  ->
         match uu____56405 with
         | (b,c) ->
             let uu____56442 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____56442 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____56505 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____56542 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____56542
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____56594 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____56638 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____56680 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____56720) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____56732) ->
          unmeta_monadic t
      | uu____56745 -> f2  in
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
      let aux f2 uu____56841 =
        match uu____56841 with
        | (lid,arity) ->
            let uu____56850 =
              let uu____56867 = unmeta_monadic f2  in
              head_and_args uu____56867  in
            (match uu____56850 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____56897 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____56897
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____56977 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____56977)
      | uu____56990 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____57057 = head_and_args t1  in
        match uu____57057 with
        | (t2,args) ->
            let uu____57112 = un_uinst t2  in
            let uu____57113 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____57154  ->
                      match uu____57154 with
                      | (t3,imp) ->
                          let uu____57173 = unascribe t3  in
                          (uu____57173, imp)))
               in
            (uu____57112, uu____57113)
         in
      let rec aux qopt out t1 =
        let uu____57224 = let uu____57248 = flat t1  in (qopt, uu____57248)
           in
        match uu____57224 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57288;
                 FStar_Syntax_Syntax.vars = uu____57289;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____57292);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____57293;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____57294;_},uu____57295)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57397;
                 FStar_Syntax_Syntax.vars = uu____57398;_},uu____57399::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____57402);
                  FStar_Syntax_Syntax.pos = uu____57403;
                  FStar_Syntax_Syntax.vars = uu____57404;_},uu____57405)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57522;
               FStar_Syntax_Syntax.vars = uu____57523;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____57526);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____57527;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____57528;_},uu____57529)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57622 =
              let uu____57626 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57626  in
            aux uu____57622 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57636;
               FStar_Syntax_Syntax.vars = uu____57637;_},uu____57638::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____57641);
                FStar_Syntax_Syntax.pos = uu____57642;
                FStar_Syntax_Syntax.vars = uu____57643;_},uu____57644)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57753 =
              let uu____57757 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57757  in
            aux uu____57753 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____57767) ->
            let bs = FStar_List.rev out  in
            let uu____57820 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____57820 with
             | (bs1,t2) ->
                 let uu____57829 = patterns t2  in
                 (match uu____57829 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____57879 -> FStar_Pervasives_Native.None  in
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
      let uu____57971 = un_squash t  in
      FStar_Util.bind_opt uu____57971
        (fun t1  ->
           let uu____57987 = head_and_args' t1  in
           match uu____57987 with
           | (hd1,args) ->
               let uu____58026 =
                 let uu____58032 =
                   let uu____58033 = un_uinst hd1  in
                   uu____58033.FStar_Syntax_Syntax.n  in
                 (uu____58032, (FStar_List.length args))  in
               (match uu____58026 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58049) when
                    (_58049 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58052) when
                    (_58052 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58055) when
                    (_58055 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58058) when
                    (_58058 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58061) when
                    (_58061 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58064) when
                    (_58064 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58067) when
                    (_58067 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58070) when
                    (_58070 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____58071 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____58101 = un_squash t  in
      FStar_Util.bind_opt uu____58101
        (fun t1  ->
           let uu____58116 = arrow_one t1  in
           match uu____58116 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____58131 =
                 let uu____58133 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____58133  in
               if uu____58131
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____58143 = comp_to_comp_typ_nouniv c  in
                    uu____58143.FStar_Syntax_Syntax.result_typ  in
                  let uu____58144 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____58144
                  then
                    let uu____58151 = patterns q  in
                    match uu____58151 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____58214 =
                       let uu____58215 =
                         let uu____58220 =
                           let uu____58221 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____58232 =
                             let uu____58243 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____58243]  in
                           uu____58221 :: uu____58232  in
                         (FStar_Parser_Const.imp_lid, uu____58220)  in
                       BaseConn uu____58215  in
                     FStar_Pervasives_Native.Some uu____58214))
           | uu____58276 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____58284 = un_squash t  in
      FStar_Util.bind_opt uu____58284
        (fun t1  ->
           let uu____58315 = head_and_args' t1  in
           match uu____58315 with
           | (hd1,args) ->
               let uu____58354 =
                 let uu____58369 =
                   let uu____58370 = un_uinst hd1  in
                   uu____58370.FStar_Syntax_Syntax.n  in
                 (uu____58369, args)  in
               (match uu____58354 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____58387)::(a2,uu____58389)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____58440 =
                      let uu____58441 = FStar_Syntax_Subst.compress a2  in
                      uu____58441.FStar_Syntax_Syntax.n  in
                    (match uu____58440 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____58448) ->
                         let uu____58483 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____58483 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____58536 -> failwith "impossible"  in
                              let uu____58544 = patterns q1  in
                              (match uu____58544 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____58605 -> FStar_Pervasives_Native.None)
                | uu____58606 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____58629 = destruct_sq_forall phi  in
          (match uu____58629 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58639  -> FStar_Pervasives_Native.Some _58639)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58646 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____58652 = destruct_sq_exists phi  in
          (match uu____58652 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58662  -> FStar_Pervasives_Native.Some _58662)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58669 -> f1)
      | uu____58672 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____58676 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____58676
      (fun uu____58681  ->
         let uu____58682 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____58682
           (fun uu____58687  ->
              let uu____58688 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____58688
                (fun uu____58693  ->
                   let uu____58694 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____58694
                     (fun uu____58699  ->
                        let uu____58700 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____58700
                          (fun uu____58704  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____58717 =
      let uu____58718 = FStar_Syntax_Subst.compress t  in
      uu____58718.FStar_Syntax_Syntax.n  in
    match uu____58717 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____58725) ->
        let uu____58760 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____58760 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____58794 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____58794
             then
               let uu____58801 =
                 let uu____58812 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____58812]  in
               mk_app t uu____58801
             else e1)
    | uu____58839 ->
        let uu____58840 =
          let uu____58851 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____58851]  in
        mk_app t uu____58840
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____58893 =
            let uu____58898 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____58898  in
          let uu____58899 =
            let uu____58900 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____58900  in
          let uu____58903 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____58893 a.FStar_Syntax_Syntax.action_univs uu____58899
            FStar_Parser_Const.effect_Tot_lid uu____58903 [] pos
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
    let uu____58929 =
      let uu____58936 =
        let uu____58937 =
          let uu____58954 =
            let uu____58965 = FStar_Syntax_Syntax.as_arg t  in [uu____58965]
             in
          (reify_1, uu____58954)  in
        FStar_Syntax_Syntax.Tm_app uu____58937  in
      FStar_Syntax_Syntax.mk uu____58936  in
    uu____58929 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____59020 =
        let uu____59027 =
          let uu____59028 =
            let uu____59029 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____59029  in
          FStar_Syntax_Syntax.Tm_constant uu____59028  in
        FStar_Syntax_Syntax.mk uu____59027  in
      uu____59020 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____59034 =
      let uu____59041 =
        let uu____59042 =
          let uu____59059 =
            let uu____59070 = FStar_Syntax_Syntax.as_arg t  in [uu____59070]
             in
          (reflect_, uu____59059)  in
        FStar_Syntax_Syntax.Tm_app uu____59042  in
      FStar_Syntax_Syntax.mk uu____59041  in
    uu____59034 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____59117 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____59142 = unfold_lazy i  in delta_qualifier uu____59142
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____59144 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____59145 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____59146 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____59169 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____59182 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____59183 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____59190 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____59191 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____59207) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____59212;
           FStar_Syntax_Syntax.index = uu____59213;
           FStar_Syntax_Syntax.sort = t2;_},uu____59215)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____59224) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____59230,uu____59231) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____59273) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____59298,t2,uu____59300) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____59325,t2) -> delta_qualifier t2
  
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
    let uu____59364 = delta_qualifier t  in incr_delta_depth uu____59364
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____59372 =
      let uu____59373 = FStar_Syntax_Subst.compress t  in
      uu____59373.FStar_Syntax_Syntax.n  in
    match uu____59372 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____59378 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____59394 =
      let uu____59411 = unmeta e  in head_and_args uu____59411  in
    match uu____59394 with
    | (head1,args) ->
        let uu____59442 =
          let uu____59457 =
            let uu____59458 = un_uinst head1  in
            uu____59458.FStar_Syntax_Syntax.n  in
          (uu____59457, args)  in
        (match uu____59442 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____59476) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____59500::(hd1,uu____59502)::(tl1,uu____59504)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____59571 =
               let uu____59574 =
                 let uu____59577 = list_elements tl1  in
                 FStar_Util.must uu____59577  in
               hd1 :: uu____59574  in
             FStar_Pervasives_Native.Some uu____59571
         | uu____59586 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____59610 .
    ('Auu____59610 -> 'Auu____59610) ->
      'Auu____59610 Prims.list -> 'Auu____59610 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____59636 = f a  in [uu____59636]
      | x::xs -> let uu____59641 = apply_last f xs  in x :: uu____59641
  
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
          let uu____59696 =
            let uu____59703 =
              let uu____59704 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____59704  in
            FStar_Syntax_Syntax.mk uu____59703  in
          uu____59696 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____59721 =
            let uu____59726 =
              let uu____59727 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59727
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59726 args  in
          uu____59721 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____59743 =
            let uu____59748 =
              let uu____59749 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59749
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59748 args  in
          uu____59743 FStar_Pervasives_Native.None pos  in
        let uu____59752 =
          let uu____59753 =
            let uu____59754 = FStar_Syntax_Syntax.iarg typ  in [uu____59754]
             in
          nil uu____59753 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____59788 =
                 let uu____59789 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____59798 =
                   let uu____59809 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____59818 =
                     let uu____59829 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____59829]  in
                   uu____59809 :: uu____59818  in
                 uu____59789 :: uu____59798  in
               cons1 uu____59788 t.FStar_Syntax_Syntax.pos) l uu____59752
  
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
        | uu____59938 -> false
  
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
          | uu____60052 -> false
  
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
        | uu____60218 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____60267 = FStar_ST.op_Bang debug_term_eq  in
          if uu____60267
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
        let t11 = let uu____60489 = unmeta_safe t1  in canon_app uu____60489
           in
        let t21 = let uu____60495 = unmeta_safe t2  in canon_app uu____60495
           in
        let uu____60498 =
          let uu____60503 =
            let uu____60504 =
              let uu____60507 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____60507  in
            uu____60504.FStar_Syntax_Syntax.n  in
          let uu____60508 =
            let uu____60509 =
              let uu____60512 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____60512  in
            uu____60509.FStar_Syntax_Syntax.n  in
          (uu____60503, uu____60508)  in
        match uu____60498 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____60514,uu____60515) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60524,FStar_Syntax_Syntax.Tm_uinst uu____60525) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____60534,uu____60535) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60560,FStar_Syntax_Syntax.Tm_delayed uu____60561) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____60586,uu____60587) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60616,FStar_Syntax_Syntax.Tm_ascribed uu____60617) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____60656 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____60656
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____60661 = FStar_Const.eq_const c1 c2  in
            check "const" uu____60661
        | (FStar_Syntax_Syntax.Tm_type
           uu____60664,FStar_Syntax_Syntax.Tm_type uu____60665) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____60723 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____60723) &&
              (let uu____60733 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____60733)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____60782 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____60782) &&
              (let uu____60792 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____60792)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____60810 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____60810)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____60867 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____60867) &&
              (let uu____60871 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____60871)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____60960 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____60960) &&
              (let uu____60964 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____60964)
        | (FStar_Syntax_Syntax.Tm_lazy uu____60981,uu____60982) ->
            let uu____60983 =
              let uu____60985 = unlazy t11  in
              term_eq_dbg dbg uu____60985 t21  in
            check "lazy_l" uu____60983
        | (uu____60987,FStar_Syntax_Syntax.Tm_lazy uu____60988) ->
            let uu____60989 =
              let uu____60991 = unlazy t21  in
              term_eq_dbg dbg t11 uu____60991  in
            check "lazy_r" uu____60989
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____61036 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____61036))
              &&
              (let uu____61040 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____61040)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____61044),FStar_Syntax_Syntax.Tm_uvar (u2,uu____61046)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____61104 =
               let uu____61106 = eq_quoteinfo qi1 qi2  in uu____61106 = Equal
                in
             check "tm_quoted qi" uu____61104) &&
              (let uu____61109 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____61109)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____61139 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____61139) &&
                   (let uu____61143 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____61143)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____61162 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____61162) &&
                    (let uu____61166 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____61166))
                   &&
                   (let uu____61170 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____61170)
             | uu____61173 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____61179) -> fail "unk"
        | (uu____61181,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____61183,uu____61184) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____61186,uu____61187) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____61189,uu____61190) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____61192,uu____61193) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____61195,uu____61196) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____61198,uu____61199) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____61219,uu____61220) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____61236,uu____61237) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____61245,uu____61246) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____61264,uu____61265) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____61289,uu____61290) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____61305,uu____61306) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____61320,uu____61321) ->
            fail "bottom"
        | (uu____61329,FStar_Syntax_Syntax.Tm_bvar uu____61330) ->
            fail "bottom"
        | (uu____61332,FStar_Syntax_Syntax.Tm_name uu____61333) ->
            fail "bottom"
        | (uu____61335,FStar_Syntax_Syntax.Tm_fvar uu____61336) ->
            fail "bottom"
        | (uu____61338,FStar_Syntax_Syntax.Tm_constant uu____61339) ->
            fail "bottom"
        | (uu____61341,FStar_Syntax_Syntax.Tm_type uu____61342) ->
            fail "bottom"
        | (uu____61344,FStar_Syntax_Syntax.Tm_abs uu____61345) ->
            fail "bottom"
        | (uu____61365,FStar_Syntax_Syntax.Tm_arrow uu____61366) ->
            fail "bottom"
        | (uu____61382,FStar_Syntax_Syntax.Tm_refine uu____61383) ->
            fail "bottom"
        | (uu____61391,FStar_Syntax_Syntax.Tm_app uu____61392) ->
            fail "bottom"
        | (uu____61410,FStar_Syntax_Syntax.Tm_match uu____61411) ->
            fail "bottom"
        | (uu____61435,FStar_Syntax_Syntax.Tm_let uu____61436) ->
            fail "bottom"
        | (uu____61451,FStar_Syntax_Syntax.Tm_uvar uu____61452) ->
            fail "bottom"
        | (uu____61466,FStar_Syntax_Syntax.Tm_meta uu____61467) ->
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
               let uu____61502 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____61502)
          (fun q1  ->
             fun q2  ->
               let uu____61514 =
                 let uu____61516 = eq_aqual q1 q2  in uu____61516 = Equal  in
               check "arg qual" uu____61514) a1 a2

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
               let uu____61541 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____61541)
          (fun q1  ->
             fun q2  ->
               let uu____61553 =
                 let uu____61555 = eq_aqual q1 q2  in uu____61555 = Equal  in
               check "binder qual" uu____61553) b1 b2

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
        ((let uu____61575 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____61575) &&
           (let uu____61579 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____61579))
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
    fun uu____61589  ->
      fun uu____61590  ->
        match (uu____61589, uu____61590) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____61717 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____61717) &&
               (let uu____61721 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____61721))
              &&
              (let uu____61725 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____61767 -> false  in
               check "branch when" uu____61725)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____61788 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____61788) &&
           (let uu____61797 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____61797))
          &&
          (let uu____61801 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____61801)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____61818 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____61818 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____61872 ->
        let uu____61895 =
          let uu____61897 = FStar_Syntax_Subst.compress t  in
          sizeof uu____61897  in
        (Prims.parse_int "1") + uu____61895
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____61900 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61900
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____61904 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61904
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____61913 = sizeof t1  in (FStar_List.length us) + uu____61913
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____61917) ->
        let uu____61942 = sizeof t1  in
        let uu____61944 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____61959  ->
                 match uu____61959 with
                 | (bv,uu____61969) ->
                     let uu____61974 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____61974) (Prims.parse_int "0") bs
           in
        uu____61942 + uu____61944
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____62003 = sizeof hd1  in
        let uu____62005 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____62020  ->
                 match uu____62020 with
                 | (arg,uu____62030) ->
                     let uu____62035 = sizeof arg  in acc + uu____62035)
            (Prims.parse_int "0") args
           in
        uu____62003 + uu____62005
    | uu____62038 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____62052 =
        let uu____62053 = un_uinst t  in uu____62053.FStar_Syntax_Syntax.n
         in
      match uu____62052 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____62058 -> false
  
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
        let uu____62107 = FStar_Options.set_options t s  in
        match uu____62107 with
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
          ((let uu____62124 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____62124 (fun a1  -> ()));
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
          let uu____62139 = FStar_Options.internal_pop ()  in
          if uu____62139
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
    | FStar_Syntax_Syntax.Tm_delayed uu____62171 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____62198 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____62213 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____62214 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____62215 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____62224) ->
        let uu____62249 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____62249 with
         | (bs1,t2) ->
             let uu____62258 =
               FStar_List.collect
                 (fun uu____62270  ->
                    match uu____62270 with
                    | (b,uu____62280) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62285 = unbound_variables t2  in
             FStar_List.append uu____62258 uu____62285)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____62310 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____62310 with
         | (bs1,c1) ->
             let uu____62319 =
               FStar_List.collect
                 (fun uu____62331  ->
                    match uu____62331 with
                    | (b,uu____62341) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62346 = unbound_variables_comp c1  in
             FStar_List.append uu____62319 uu____62346)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____62355 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____62355 with
         | (bs,t2) ->
             let uu____62378 =
               FStar_List.collect
                 (fun uu____62390  ->
                    match uu____62390 with
                    | (b1,uu____62400) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____62405 = unbound_variables t2  in
             FStar_List.append uu____62378 uu____62405)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____62434 =
          FStar_List.collect
            (fun uu____62448  ->
               match uu____62448 with
               | (x,uu____62460) -> unbound_variables x) args
           in
        let uu____62469 = unbound_variables t1  in
        FStar_List.append uu____62434 uu____62469
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____62510 = unbound_variables t1  in
        let uu____62513 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____62528 = FStar_Syntax_Subst.open_branch br  in
                  match uu____62528 with
                  | (p,wopt,t2) ->
                      let uu____62550 = unbound_variables t2  in
                      let uu____62553 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____62550 uu____62553))
           in
        FStar_List.append uu____62510 uu____62513
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____62567) ->
        let uu____62608 = unbound_variables t1  in
        let uu____62611 =
          let uu____62614 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____62645 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____62614 uu____62645  in
        FStar_List.append uu____62608 uu____62611
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____62686 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____62689 =
          let uu____62692 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____62695 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____62700 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____62702 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____62702 with
                 | (uu____62723,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____62692 uu____62695  in
        FStar_List.append uu____62686 uu____62689
    | FStar_Syntax_Syntax.Tm_let ((uu____62725,lbs),t1) ->
        let uu____62745 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____62745 with
         | (lbs1,t2) ->
             let uu____62760 = unbound_variables t2  in
             let uu____62763 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____62770 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____62773 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____62770 uu____62773) lbs1
                in
             FStar_List.append uu____62760 uu____62763)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____62790 = unbound_variables t1  in
        let uu____62793 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____62832  ->
                      match uu____62832 with
                      | (a,uu____62844) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____62853,uu____62854,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____62860,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____62866 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____62875 -> []
          | FStar_Syntax_Syntax.Meta_named uu____62876 -> []  in
        FStar_List.append uu____62790 uu____62793

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____62883) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____62893) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____62903 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____62906 =
          FStar_List.collect
            (fun uu____62920  ->
               match uu____62920 with
               | (a,uu____62932) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____62903 uu____62906

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
            let uu____63047 = head_and_args h  in
            (match uu____63047 with
             | (head1,args) ->
                 let uu____63108 =
                   let uu____63109 = FStar_Syntax_Subst.compress head1  in
                   uu____63109.FStar_Syntax_Syntax.n  in
                 (match uu____63108 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____63162 -> aux (h :: acc) t))
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
      let uu____63186 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____63186 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2985_63228 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2985_63228.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2985_63228.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2985_63228.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2985_63228.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  