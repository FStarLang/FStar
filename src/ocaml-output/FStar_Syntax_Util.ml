open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____41062 = FStar_ST.op_Bang tts_f  in
    match uu____41062 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____41126 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____41126 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____41133 =
      let uu____41136 =
        let uu____41139 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____41139]  in
      FStar_List.append lid.FStar_Ident.ns uu____41136  in
    FStar_Ident.lid_of_ids uu____41133
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____41157 .
    (FStar_Syntax_Syntax.bv * 'Auu____41157) ->
      (FStar_Syntax_Syntax.term * 'Auu____41157)
  =
  fun uu____41170  ->
    match uu____41170 with
    | (b,imp) ->
        let uu____41177 = FStar_Syntax_Syntax.bv_to_name b  in
        (uu____41177, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____41229 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____41229
            then []
            else
              (let uu____41248 = arg_of_non_null_binder b  in [uu____41248])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____41283 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____41365 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____41365
              then
                let b1 =
                  let uu____41391 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____41391, (FStar_Pervasives_Native.snd b))  in
                let uu____41398 = arg_of_non_null_binder b1  in
                (b1, uu____41398)
              else
                (let uu____41421 = arg_of_non_null_binder b  in
                 (b, uu____41421))))
       in
    FStar_All.pipe_right uu____41283 FStar_List.unzip
  
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
              let uu____41555 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____41555
              then
                let uu____41564 = b  in
                match uu____41564 with
                | (a,imp) ->
                    let b1 =
                      let uu____41584 =
                        let uu____41586 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____41586  in
                      FStar_Ident.id_of_text uu____41584  in
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
        let uu____41631 =
          let uu____41638 =
            let uu____41639 =
              let uu____41654 = name_binders binders  in (uu____41654, comp)
               in
            FStar_Syntax_Syntax.Tm_arrow uu____41639  in
          FStar_Syntax_Syntax.mk uu____41638  in
        uu____41631 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____41673 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____41710  ->
            match uu____41710 with
            | (t,imp) ->
                let uu____41721 =
                  let uu____41722 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____41722
                   in
                (uu____41721, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____41777  ->
            match uu____41777 with
            | (t,imp) ->
                let uu____41794 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____41794, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____41807 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____41807
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____41819 . 'Auu____41819 -> 'Auu____41819 Prims.list =
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
          (fun uu____41945  ->
             fun uu____41946  ->
               match (uu____41945, uu____41946) with
               | ((x,uu____41972),(y,uu____41974)) ->
                   let uu____41995 =
                     let uu____42002 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____42002)  in
                   FStar_Syntax_Syntax.NT uu____41995) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____42018) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____42024,uu____42025) ->
        unmeta e2
    | uu____42066 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____42080 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____42087 -> e1
         | uu____42096 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____42098,uu____42099) ->
        unmeta_safe e2
    | uu____42140 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____42159 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____42162 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____42176 = univ_kernel u1  in
        (match uu____42176 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____42193 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____42202 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____42217 = univ_kernel u  in
    FStar_Pervasives_Native.snd uu____42217
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____42237,uu____42238) ->
          failwith "Impossible: compare_univs"
      | (uu____42242,FStar_Syntax_Syntax.U_bvar uu____42243) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____42248) ->
          ~- (Prims.parse_int "1")
      | (uu____42250,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____42253) -> ~- (Prims.parse_int "1")
      | (uu____42255,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____42259,FStar_Syntax_Syntax.U_unif
         uu____42260) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____42270,FStar_Syntax_Syntax.U_name
         uu____42271) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____42299 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____42301 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____42299 - uu____42301
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____42319 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____42319
                 (fun uu____42335  ->
                    match uu____42335 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____42363,uu____42364) ->
          ~- (Prims.parse_int "1")
      | (uu____42368,FStar_Syntax_Syntax.U_max uu____42369) ->
          (Prims.parse_int "1")
      | uu____42373 ->
          let uu____42378 = univ_kernel u1  in
          (match uu____42378 with
           | (k1,n1) ->
               let uu____42389 = univ_kernel u2  in
               (match uu____42389 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____42420 = compare_univs u1 u2  in
      uu____42420 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____42439 =
        let uu____42440 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____42440;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____42439
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____42460 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____42469 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____42492 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____42501 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____42528 =
          let uu____42529 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____42529  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____42528;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____42558 =
          let uu____42559 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____42559  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____42558;
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
      let uu___631_42595 = c  in
      let uu____42596 =
        let uu____42597 =
          let uu___633_42598 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___633_42598.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___633_42598.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___633_42598.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___633_42598.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____42597  in
      {
        FStar_Syntax_Syntax.n = uu____42596;
        FStar_Syntax_Syntax.pos = (uu___631_42595.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___631_42595.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____42624 -> c
        | FStar_Syntax_Syntax.GTotal uu____42633 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___645_42644 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___645_42644.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___645_42644.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___645_42644.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___645_42644.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___648_42645 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___648_42645.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___648_42645.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____42648  ->
           let uu____42649 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____42649)
  
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
    | uu____42689 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____42704 -> true
    | FStar_Syntax_Syntax.GTotal uu____42714 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___402_42739  ->
               match uu___402_42739 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____42743 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___403_42756  ->
               match uu___403_42756 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____42760 -> false)))
  
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
            (fun uu___404_42773  ->
               match uu___404_42773 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____42777 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___405_42794  ->
            match uu___405_42794 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____42798 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___406_42811  ->
            match uu___406_42811 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____42815 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____42847 -> true
    | FStar_Syntax_Syntax.GTotal uu____42857 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___407_42872  ->
                   match uu___407_42872 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____42875 -> false)))
  
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
            (fun uu___408_42920  ->
               match uu___408_42920 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____42923 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____42939 =
      let uu____42940 = FStar_Syntax_Subst.compress t  in
      uu____42940.FStar_Syntax_Syntax.n  in
    match uu____42939 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____42944,c) -> is_pure_or_ghost_comp c
    | uu____42966 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____42981 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____42990 =
      let uu____42991 = FStar_Syntax_Subst.compress t  in
      uu____42991.FStar_Syntax_Syntax.n  in
    match uu____42990 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____42995,c) -> is_lemma_comp c
    | uu____43017 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____43025 =
      let uu____43026 = FStar_Syntax_Subst.compress t  in
      uu____43026.FStar_Syntax_Syntax.n  in
    match uu____43025 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____43030) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____43056) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____43093,t1,uu____43095) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____43121,uu____43122) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____43164) -> head_of t1
    | uu____43169 -> t
  
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
    | uu____43247 -> (t1, [])
  
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
        let uu____43329 = head_and_args' head1  in
        (match uu____43329 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____43398 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____43425) ->
        FStar_Syntax_Subst.compress t2
    | uu____43430 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____43438 =
      let uu____43439 = FStar_Syntax_Subst.compress t  in
      uu____43439.FStar_Syntax_Syntax.n  in
    match uu____43438 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____43443,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____43471)::uu____43472 ->
                  let pats' = unmeta pats  in
                  let uu____43532 = head_and_args pats'  in
                  (match uu____43532 with
                   | (head1,uu____43551) ->
                       let uu____43576 =
                         let uu____43577 = un_uinst head1  in
                         uu____43577.FStar_Syntax_Syntax.n  in
                       (match uu____43576 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____43582 -> false))
              | uu____43584 -> false)
         | uu____43596 -> false)
    | uu____43598 -> false
  
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
                (fun uu___409_43617  ->
                   match uu___409_43617 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____43620 -> false)))
    | uu____43622 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____43639) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____43649) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____43678 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____43687 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___827_43699 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___827_43699.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___827_43699.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___827_43699.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___827_43699.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____43713  ->
           let uu____43714 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____43714 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___410_43732  ->
            match uu___410_43732 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____43736 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____43744 -> []
    | FStar_Syntax_Syntax.GTotal uu____43761 -> []
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
    | uu____43805 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____43815,uu____43816) ->
        unascribe e2
    | uu____43857 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____43910,uu____43911) ->
          ascribe t' k
      | uu____43952 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____43979 =
      let uu____43988 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____43988  in
    uu____43979 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____44044 =
      let uu____44045 = FStar_Syntax_Subst.compress t  in
      uu____44045.FStar_Syntax_Syntax.n  in
    match uu____44044 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____44049 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____44049
    | uu____44050 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____44057 =
      let uu____44058 = FStar_Syntax_Subst.compress t  in
      uu____44058.FStar_Syntax_Syntax.n  in
    match uu____44057 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____44062 ->
             let uu____44071 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____44071
         | uu____44072 -> t)
    | uu____44073 -> t
  
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
      | uu____44097 -> false
  
let rec unlazy_as_t :
  'Auu____44110 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_Syntax_Syntax.term -> 'Auu____44110
  =
  fun k  ->
    fun t  ->
      let uu____44121 =
        let uu____44122 = FStar_Syntax_Subst.compress t  in
        uu____44122.FStar_Syntax_Syntax.n  in
      match uu____44121 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____44127;
            FStar_Syntax_Syntax.rng = uu____44128;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____44131 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____44172 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____44172;
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
    let uu____44185 =
      let uu____44200 = unascribe t  in head_and_args' uu____44200  in
    match uu____44185 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____44234 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____44245 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____44256 -> false
  
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
      | (NotEqual ,uu____44306) -> NotEqual
      | (uu____44307,NotEqual ) -> NotEqual
      | (Unknown ,uu____44308) -> Unknown
      | (uu____44309,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___411_44430 = if uu___411_44430 then Equal else Unknown
         in
      let equal_iff uu___412_44441 =
        if uu___412_44441 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____44462 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____44484 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____44484
        then
          let uu____44488 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____44565  ->
                    match uu____44565 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____44606 = eq_tm a1 a2  in
                        eq_inj acc uu____44606) Equal) uu____44488
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____44620 =
          let uu____44637 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____44637 head_and_args  in
        match uu____44620 with
        | (head1,args1) ->
            let uu____44690 =
              let uu____44707 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____44707 head_and_args  in
            (match uu____44690 with
             | (head2,args2) ->
                 let uu____44760 =
                   let uu____44765 =
                     let uu____44766 = un_uinst head1  in
                     uu____44766.FStar_Syntax_Syntax.n  in
                   let uu____44769 =
                     let uu____44770 = un_uinst head2  in
                     uu____44770.FStar_Syntax_Syntax.n  in
                   (uu____44765, uu____44769)  in
                 (match uu____44760 with
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
                  | uu____44797 -> FStar_Pervasives_Native.None))
         in
      let uu____44810 =
        let uu____44815 =
          let uu____44816 = unmeta t11  in uu____44816.FStar_Syntax_Syntax.n
           in
        let uu____44819 =
          let uu____44820 = unmeta t21  in uu____44820.FStar_Syntax_Syntax.n
           in
        (uu____44815, uu____44819)  in
      match uu____44810 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____44826,uu____44827) ->
          let uu____44828 = unlazy t11  in eq_tm uu____44828 t21
      | (uu____44829,FStar_Syntax_Syntax.Tm_lazy uu____44830) ->
          let uu____44831 = unlazy t21  in eq_tm t11 uu____44831
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____44834 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____44858 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____44858
            (fun uu____44906  ->
               match uu____44906 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____44921 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____44921
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____44935 = eq_tm f g  in
          eq_and uu____44935
            (fun uu____44938  ->
               let uu____44939 = eq_univs_list us vs  in equal_if uu____44939)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____44941),uu____44942) -> Unknown
      | (uu____44943,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____44944)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____44947 = FStar_Const.eq_const c d  in
          equal_iff uu____44947
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____44950)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____44952))) ->
          let uu____44981 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____44981
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____45035 =
            let uu____45040 =
              let uu____45041 = un_uinst h1  in
              uu____45041.FStar_Syntax_Syntax.n  in
            let uu____45044 =
              let uu____45045 = un_uinst h2  in
              uu____45045.FStar_Syntax_Syntax.n  in
            (uu____45040, uu____45044)  in
          (match uu____45035 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____45051 =
                    let uu____45053 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____45053  in
                  FStar_List.mem uu____45051 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____45055 ->
               let uu____45060 = eq_tm h1 h2  in
               eq_and uu____45060 (fun uu____45062  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____45168 = FStar_List.zip bs1 bs2  in
            let uu____45231 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____45268  ->
                 fun a  ->
                   match uu____45268 with
                   | (b1,b2) ->
                       eq_and a (fun uu____45361  -> branch_matches b1 b2))
              uu____45168 uu____45231
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____45366 = eq_univs u v1  in equal_if uu____45366
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____45380 = eq_quoteinfo q1 q2  in
          eq_and uu____45380 (fun uu____45382  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____45395 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____45395 (fun uu____45397  -> eq_tm phi1 phi2)
      | uu____45398 -> Unknown

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
      | ([],uu____45470) -> NotEqual
      | (uu____45501,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____45593 = eq_tm t1 t2  in
             match uu____45593 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____45594 = eq_antiquotes a11 a21  in
                 (match uu____45594 with
                  | NotEqual  -> NotEqual
                  | uu____45595 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____45610) -> NotEqual
      | (uu____45617,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____45647 -> NotEqual

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
        | (uu____45739,uu____45740) -> false  in
      let uu____45750 = b1  in
      match uu____45750 with
      | (p1,w1,t1) ->
          let uu____45784 = b2  in
          (match uu____45784 with
           | (p2,w2,t2) ->
               let uu____45818 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____45818
               then
                 let uu____45821 =
                   (let uu____45825 = eq_tm t1 t2  in uu____45825 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____45834 = eq_tm t11 t21  in
                             uu____45834 = Equal) w1 w2)
                    in
                 (if uu____45821 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____45899)::a11,(b,uu____45902)::b1) ->
          let uu____45976 = eq_tm a b  in
          (match uu____45976 with
           | Equal  -> eq_args a11 b1
           | uu____45977 -> Unknown)
      | uu____45978 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____46014) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____46020,uu____46021) ->
        unrefine t2
    | uu____46062 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46070 =
      let uu____46071 = FStar_Syntax_Subst.compress t  in
      uu____46071.FStar_Syntax_Syntax.n  in
    match uu____46070 with
    | FStar_Syntax_Syntax.Tm_uvar uu____46075 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____46090) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____46095 ->
        let uu____46112 =
          let uu____46113 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____46113 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____46112 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____46176,uu____46177) ->
        is_uvar t1
    | uu____46218 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46227 =
      let uu____46228 = unrefine t  in uu____46228.FStar_Syntax_Syntax.n  in
    match uu____46227 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____46234) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____46260) -> is_unit t1
    | uu____46265 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46274 =
      let uu____46275 = FStar_Syntax_Subst.compress t  in
      uu____46275.FStar_Syntax_Syntax.n  in
    match uu____46274 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____46280 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46289 =
      let uu____46290 = unrefine t  in uu____46290.FStar_Syntax_Syntax.n  in
    match uu____46289 with
    | FStar_Syntax_Syntax.Tm_type uu____46294 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____46298) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____46324) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____46329,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____46351 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____46360 =
      let uu____46361 = FStar_Syntax_Subst.compress e  in
      uu____46361.FStar_Syntax_Syntax.n  in
    match uu____46360 with
    | FStar_Syntax_Syntax.Tm_abs uu____46365 -> true
    | uu____46385 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46394 =
      let uu____46395 = FStar_Syntax_Subst.compress t  in
      uu____46395.FStar_Syntax_Syntax.n  in
    match uu____46394 with
    | FStar_Syntax_Syntax.Tm_arrow uu____46399 -> true
    | uu____46415 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____46425) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____46431,uu____46432) ->
        pre_typ t2
    | uu____46473 -> t1
  
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
      let uu____46498 =
        let uu____46499 = un_uinst typ1  in uu____46499.FStar_Syntax_Syntax.n
         in
      match uu____46498 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____46564 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____46594 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____46615,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____46622) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____46627,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____46638,uu____46639,uu____46640,uu____46641,uu____46642) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____46652,uu____46653,uu____46654,uu____46655) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____46661,uu____46662,uu____46663,uu____46664,uu____46665) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____46673,uu____46674) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____46676,uu____46677) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____46680 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____46681 -> []
    | FStar_Syntax_Syntax.Sig_main uu____46682 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____46696 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___413_46722  ->
    match uu___413_46722 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____46736 'Auu____46737 .
    ('Auu____46736 FStar_Syntax_Syntax.syntax * 'Auu____46737) ->
      FStar_Range.range
  =
  fun uu____46748  ->
    match uu____46748 with | (hd1,uu____46756) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____46770 'Auu____46771 .
    ('Auu____46770 FStar_Syntax_Syntax.syntax * 'Auu____46771) Prims.list ->
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
      | uu____46869 ->
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
      let uu____46928 =
        FStar_List.map
          (fun uu____46955  ->
             match uu____46955 with
             | (bv,aq) ->
                 let uu____46974 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____46974, aq)) bs
         in
      mk_app f uu____46928
  
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
          let uu____47024 = FStar_Ident.range_of_lid l  in
          let uu____47025 =
            let uu____47034 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____47034  in
          uu____47025 FStar_Pervasives_Native.None uu____47024
      | uu____47039 ->
          let e =
            let uu____47053 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____47053 args  in
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
          let uu____47130 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____47130
          then
            let uu____47133 =
              let uu____47139 =
                let uu____47141 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____47141  in
              let uu____47144 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____47139, uu____47144)  in
            FStar_Ident.mk_ident uu____47133
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___1421_47149 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___1421_47149.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___1421_47149.FStar_Syntax_Syntax.sort)
          }  in
        let uu____47150 = mk_field_projector_name_from_ident lid nm  in
        (uu____47150, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____47162) -> ses
    | uu____47171 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____47182 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____47195 = FStar_Syntax_Unionfind.find uv  in
      match uu____47195 with
      | FStar_Pervasives_Native.Some uu____47198 ->
          let uu____47199 =
            let uu____47201 =
              let uu____47203 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____47203  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____47201  in
          failwith uu____47199
      | uu____47208 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____47291 -> q1 = q2
  
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
              let uu____47337 =
                let uu___1482_47338 = rc  in
                let uu____47339 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1482_47338.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____47339;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1482_47338.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____47337
           in
        match bs with
        | [] -> t
        | uu____47356 ->
            let body =
              let uu____47358 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____47358  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____47388 =
                   let uu____47395 =
                     let uu____47396 =
                       let uu____47415 =
                         let uu____47424 =
                           FStar_Syntax_Subst.close_binders bs  in
                         FStar_List.append uu____47424 bs'  in
                       let uu____47439 = close_lopt lopt'  in
                       (uu____47415, t1, uu____47439)  in
                     FStar_Syntax_Syntax.Tm_abs uu____47396  in
                   FStar_Syntax_Syntax.mk uu____47395  in
                 uu____47388 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____47454 ->
                 let uu____47455 =
                   let uu____47462 =
                     let uu____47463 =
                       let uu____47482 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____47491 = close_lopt lopt  in
                       (uu____47482, body, uu____47491)  in
                     FStar_Syntax_Syntax.Tm_abs uu____47463  in
                   FStar_Syntax_Syntax.mk uu____47462  in
                 uu____47455 FStar_Pervasives_Native.None
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
      | uu____47547 ->
          let uu____47556 =
            let uu____47563 =
              let uu____47564 =
                let uu____47579 = FStar_Syntax_Subst.close_binders bs  in
                let uu____47588 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____47579, uu____47588)  in
              FStar_Syntax_Syntax.Tm_arrow uu____47564  in
            FStar_Syntax_Syntax.mk uu____47563  in
          uu____47556 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____47637 =
        let uu____47638 = FStar_Syntax_Subst.compress t  in
        uu____47638.FStar_Syntax_Syntax.n  in
      match uu____47637 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____47668) ->
               let uu____47677 =
                 let uu____47678 = FStar_Syntax_Subst.compress tres  in
                 uu____47678.FStar_Syntax_Syntax.n  in
               (match uu____47677 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____47721 -> t)
           | uu____47722 -> t)
      | uu____47723 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____47741 =
        let uu____47742 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____47742 t.FStar_Syntax_Syntax.pos  in
      let uu____47743 =
        let uu____47750 =
          let uu____47751 =
            let uu____47758 =
              let uu____47761 =
                let uu____47762 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____47762]  in
              FStar_Syntax_Subst.close uu____47761 t  in
            (b, uu____47758)  in
          FStar_Syntax_Syntax.Tm_refine uu____47751  in
        FStar_Syntax_Syntax.mk uu____47750  in
      uu____47743 FStar_Pervasives_Native.None uu____47741
  
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
        let uu____47842 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____47842 with
         | (bs1,c1) ->
             let uu____47861 = is_total_comp c1  in
             if uu____47861
             then
               let uu____47876 = arrow_formals_comp (comp_result c1)  in
               (match uu____47876 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____47943;
           FStar_Syntax_Syntax.index = uu____47944;
           FStar_Syntax_Syntax.sort = s;_},uu____47946)
        ->
        let rec aux s1 k2 =
          let uu____47977 =
            let uu____47978 = FStar_Syntax_Subst.compress s1  in
            uu____47978.FStar_Syntax_Syntax.n  in
          match uu____47977 with
          | FStar_Syntax_Syntax.Tm_arrow uu____47993 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____48008;
                 FStar_Syntax_Syntax.index = uu____48009;
                 FStar_Syntax_Syntax.sort = s2;_},uu____48011)
              -> aux s2 k2
          | uu____48019 ->
              let uu____48020 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____48020)
           in
        aux s k1
    | uu____48035 ->
        let uu____48036 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____48036)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____48071 = arrow_formals_comp k  in
    match uu____48071 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____48213 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____48213 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____48237 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___414_48246  ->
                         match uu___414_48246 with
                         | FStar_Syntax_Syntax.DECREASES uu____48248 -> true
                         | uu____48252 -> false))
                  in
               (match uu____48237 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____48287 ->
                    let uu____48290 = is_total_comp c1  in
                    if uu____48290
                    then
                      let uu____48309 =
                        arrow_until_decreases (comp_result c1)  in
                      (match uu____48309 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____48402;
             FStar_Syntax_Syntax.index = uu____48403;
             FStar_Syntax_Syntax.sort = k2;_},uu____48405)
          -> arrow_until_decreases k2
      | uu____48413 -> ([], FStar_Pervasives_Native.None)  in
    let uu____48434 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____48434 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____48488 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____48509 =
                 FStar_Common.tabulate n_univs (fun uu____48515  -> false)
                  in
               let uu____48518 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____48543  ->
                         match uu____48543 with
                         | (x,uu____48552) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____48509 uu____48518)
           in
        ((n_univs + (FStar_List.length bs)), uu____48488)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____48608 =
            let uu___1604_48609 = rc  in
            let uu____48610 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1604_48609.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____48610;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1604_48609.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____48608
      | uu____48619 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____48653 =
        let uu____48654 =
          let uu____48657 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____48657  in
        uu____48654.FStar_Syntax_Syntax.n  in
      match uu____48653 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____48703 = aux t2 what  in
          (match uu____48703 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____48775 -> ([], t1, abs_body_lcomp)  in
    let uu____48792 = aux t FStar_Pervasives_Native.None  in
    match uu____48792 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____48840 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____48840 with
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
                    | (FStar_Pervasives_Native.None ,uu____49003) -> def
                    | (uu____49014,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____49026) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _49042  ->
                                  FStar_Syntax_Syntax.U_name _49042))
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
            let uu____49124 = FStar_Syntax_Subst.open_univ_vars_comp uvs c
               in
            (match uu____49124 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____49159 ->
            let t' = arrow binders c  in
            let uu____49171 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____49171 with
             | (uvs1,t'1) ->
                 let uu____49192 =
                   let uu____49193 = FStar_Syntax_Subst.compress t'1  in
                   uu____49193.FStar_Syntax_Syntax.n  in
                 (match uu____49192 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____49242 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____49267 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____49278 -> false
  
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
      let uu____49341 =
        let uu____49342 = pre_typ t  in uu____49342.FStar_Syntax_Syntax.n  in
      match uu____49341 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____49347 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____49361 =
        let uu____49362 = pre_typ t  in uu____49362.FStar_Syntax_Syntax.n  in
      match uu____49361 with
      | FStar_Syntax_Syntax.Tm_fvar uu____49366 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____49368) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____49394) ->
          is_constructed_typ t1 lid
      | uu____49399 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____49412 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____49413 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____49414 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____49416) -> get_tycon t2
    | uu____49441 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____49449 =
      let uu____49450 = un_uinst t  in uu____49450.FStar_Syntax_Syntax.n  in
    match uu____49449 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____49455 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____49469 =
        let uu____49473 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____49473  in
      match uu____49469 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____49505 -> false
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
  fun uu____49524  ->
    let u =
      let uu____49530 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _49547  -> FStar_Syntax_Syntax.U_unif _49547)
        uu____49530
       in
    let uu____49548 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____49548, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____49561 = eq_tm a a'  in
      match uu____49561 with | Equal  -> true | uu____49564 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____49569 =
    let uu____49576 =
      let uu____49577 =
        let uu____49578 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____49578
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____49577  in
    FStar_Syntax_Syntax.mk uu____49576  in
  uu____49569 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____49690 =
            let uu____49693 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____49694 =
              let uu____49701 =
                let uu____49702 =
                  let uu____49719 =
                    let uu____49730 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____49739 =
                      let uu____49750 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____49750]  in
                    uu____49730 :: uu____49739  in
                  (tand, uu____49719)  in
                FStar_Syntax_Syntax.Tm_app uu____49702  in
              FStar_Syntax_Syntax.mk uu____49701  in
            uu____49694 FStar_Pervasives_Native.None uu____49693  in
          FStar_Pervasives_Native.Some uu____49690
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____49827 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____49828 =
          let uu____49835 =
            let uu____49836 =
              let uu____49853 =
                let uu____49864 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____49873 =
                  let uu____49884 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____49884]  in
                uu____49864 :: uu____49873  in
              (op_t, uu____49853)  in
            FStar_Syntax_Syntax.Tm_app uu____49836  in
          FStar_Syntax_Syntax.mk uu____49835  in
        uu____49828 FStar_Pervasives_Native.None uu____49827
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____49941 =
      let uu____49948 =
        let uu____49949 =
          let uu____49966 =
            let uu____49977 = FStar_Syntax_Syntax.as_arg phi  in
            [uu____49977]  in
          (t_not, uu____49966)  in
        FStar_Syntax_Syntax.Tm_app uu____49949  in
      FStar_Syntax_Syntax.mk uu____49948  in
    uu____49941 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____50174 =
      let uu____50181 =
        let uu____50182 =
          let uu____50199 =
            let uu____50210 = FStar_Syntax_Syntax.as_arg e  in [uu____50210]
             in
          (b2t_v, uu____50199)  in
        FStar_Syntax_Syntax.Tm_app uu____50182  in
      FStar_Syntax_Syntax.mk uu____50181  in
    uu____50174 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50254 =
      let uu____50255 = unmeta t  in uu____50255.FStar_Syntax_Syntax.n  in
    match uu____50254 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____50260 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____50283 = is_t_true t1  in
      if uu____50283
      then t2
      else
        (let uu____50290 = is_t_true t2  in
         if uu____50290 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____50318 = is_t_true t1  in
      if uu____50318
      then t_true
      else
        (let uu____50325 = is_t_true t2  in
         if uu____50325 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____50354 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____50355 =
        let uu____50362 =
          let uu____50363 =
            let uu____50380 =
              let uu____50391 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____50400 =
                let uu____50411 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____50411]  in
              uu____50391 :: uu____50400  in
            (teq, uu____50380)  in
          FStar_Syntax_Syntax.Tm_app uu____50363  in
        FStar_Syntax_Syntax.mk uu____50362  in
      uu____50355 FStar_Pervasives_Native.None uu____50354
  
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
          let uu____50478 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____50479 =
            let uu____50486 =
              let uu____50487 =
                let uu____50504 =
                  let uu____50515 = FStar_Syntax_Syntax.iarg t  in
                  let uu____50524 =
                    let uu____50535 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____50544 =
                      let uu____50555 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____50555]  in
                    uu____50535 :: uu____50544  in
                  uu____50515 :: uu____50524  in
                (eq_inst, uu____50504)  in
              FStar_Syntax_Syntax.Tm_app uu____50487  in
            FStar_Syntax_Syntax.mk uu____50486  in
          uu____50479 FStar_Pervasives_Native.None uu____50478
  
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
        let uu____50632 =
          let uu____50639 =
            let uu____50640 =
              let uu____50657 =
                let uu____50668 = FStar_Syntax_Syntax.iarg t  in
                let uu____50677 =
                  let uu____50688 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____50697 =
                    let uu____50708 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____50708]  in
                  uu____50688 :: uu____50697  in
                uu____50668 :: uu____50677  in
              (t_has_type1, uu____50657)  in
            FStar_Syntax_Syntax.Tm_app uu____50640  in
          FStar_Syntax_Syntax.mk uu____50639  in
        uu____50632 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____50785 =
          let uu____50792 =
            let uu____50793 =
              let uu____50810 =
                let uu____50821 = FStar_Syntax_Syntax.iarg t  in
                let uu____50830 =
                  let uu____50841 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____50841]  in
                uu____50821 :: uu____50830  in
              (t_with_type1, uu____50810)  in
            FStar_Syntax_Syntax.Tm_app uu____50793  in
          FStar_Syntax_Syntax.mk uu____50792  in
        uu____50785 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____50888 =
    let uu____50895 =
      let uu____50896 =
        let uu____50903 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____50903, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____50896  in
    FStar_Syntax_Syntax.mk uu____50895  in
  uu____50888 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____50918 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____50931 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____50942 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____50918 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____50963  -> c0)
  
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
        let uu____51046 =
          let uu____51053 =
            let uu____51054 =
              let uu____51071 =
                let uu____51082 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____51091 =
                  let uu____51102 =
                    let uu____51111 =
                      let uu____51112 =
                        let uu____51113 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____51113]  in
                      abs uu____51112 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____51111  in
                  [uu____51102]  in
                uu____51082 :: uu____51091  in
              (fa, uu____51071)  in
            FStar_Syntax_Syntax.Tm_app uu____51054  in
          FStar_Syntax_Syntax.mk uu____51053  in
        uu____51046 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____51240 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____51240
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____51259 -> true
    | uu____51261 -> false
  
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
          let uu____51308 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____51308, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____51337 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____51337, FStar_Pervasives_Native.None, t2)  in
        let uu____51351 =
          let uu____51352 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____51352  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____51351
  
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
      let uu____51428 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____51431 =
        let uu____51442 = FStar_Syntax_Syntax.as_arg p  in [uu____51442]  in
      mk_app uu____51428 uu____51431
  
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
      let uu____51482 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____51485 =
        let uu____51496 = FStar_Syntax_Syntax.as_arg p  in [uu____51496]  in
      mk_app uu____51482 uu____51485
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51531 = head_and_args t  in
    match uu____51531 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____51580 =
          let uu____51595 =
            let uu____51596 = FStar_Syntax_Subst.compress head3  in
            uu____51596.FStar_Syntax_Syntax.n  in
          (uu____51595, args)  in
        (match uu____51580 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____51615)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____51681 =
                    let uu____51686 =
                      let uu____51687 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____51687]  in
                    FStar_Syntax_Subst.open_term uu____51686 p  in
                  (match uu____51681 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____51744 -> failwith "impossible"  in
                       let uu____51752 =
                         let uu____51754 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____51754
                          in
                       if uu____51752
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____51770 -> FStar_Pervasives_Native.None)
         | uu____51773 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51804 = head_and_args t  in
    match uu____51804 with
    | (head1,args) ->
        let uu____51855 =
          let uu____51870 =
            let uu____51871 = FStar_Syntax_Subst.compress head1  in
            uu____51871.FStar_Syntax_Syntax.n  in
          (uu____51870, args)  in
        (match uu____51855 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____51893;
               FStar_Syntax_Syntax.vars = uu____51894;_},u::[]),(t1,uu____51897)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____51944 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51979 = head_and_args t  in
    match uu____51979 with
    | (head1,args) ->
        let uu____52030 =
          let uu____52045 =
            let uu____52046 = FStar_Syntax_Subst.compress head1  in
            uu____52046.FStar_Syntax_Syntax.n  in
          (uu____52045, args)  in
        (match uu____52030 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____52068;
               FStar_Syntax_Syntax.vars = uu____52069;_},u::[]),(t1,uu____52072)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____52119 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____52147 =
      let uu____52164 = unmeta t  in head_and_args uu____52164  in
    match uu____52147 with
    | (head1,uu____52167) ->
        let uu____52192 =
          let uu____52193 = un_uinst head1  in
          uu____52193.FStar_Syntax_Syntax.n  in
        (match uu____52192 with
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
         | uu____52198 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____52218 =
      let uu____52231 =
        let uu____52232 = FStar_Syntax_Subst.compress t  in
        uu____52232.FStar_Syntax_Syntax.n  in
      match uu____52231 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____52362 =
            let uu____52373 =
              let uu____52374 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____52374  in
            (b, uu____52373)  in
          FStar_Pervasives_Native.Some uu____52362
      | uu____52391 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____52218
      (fun uu____52429  ->
         match uu____52429 with
         | (b,c) ->
             let uu____52466 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____52466 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____52529 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____52566 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____52566
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____52618 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____52662 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____52704 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____52744) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____52756) ->
          unmeta_monadic t
      | uu____52769 -> f2  in
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
      let aux f2 uu____52865 =
        match uu____52865 with
        | (lid,arity) ->
            let uu____52874 =
              let uu____52891 = unmeta_monadic f2  in
              head_and_args uu____52891  in
            (match uu____52874 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____52921 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____52921
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____52997 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____52997)
      | uu____53010 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____53077 = head_and_args t1  in
        match uu____53077 with
        | (t2,args) ->
            let uu____53132 = un_uinst t2  in
            let uu____53133 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____53174  ->
                      match uu____53174 with
                      | (t3,imp) ->
                          let uu____53193 = unascribe t3  in
                          (uu____53193, imp)))
               in
            (uu____53132, uu____53133)
         in
      let rec aux qopt out t1 =
        let uu____53244 = let uu____53268 = flat t1  in (qopt, uu____53268)
           in
        match uu____53244 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____53308;
                 FStar_Syntax_Syntax.vars = uu____53309;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____53312);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____53313;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____53314;_},uu____53315)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____53417;
                 FStar_Syntax_Syntax.vars = uu____53418;_},uu____53419::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____53422);
                  FStar_Syntax_Syntax.pos = uu____53423;
                  FStar_Syntax_Syntax.vars = uu____53424;_},uu____53425)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____53542;
               FStar_Syntax_Syntax.vars = uu____53543;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____53546);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____53547;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____53548;_},uu____53549)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____53642 =
              let uu____53646 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____53646  in
            aux uu____53642 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____53656;
               FStar_Syntax_Syntax.vars = uu____53657;_},uu____53658::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____53661);
                FStar_Syntax_Syntax.pos = uu____53662;
                FStar_Syntax_Syntax.vars = uu____53663;_},uu____53664)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____53773 =
              let uu____53777 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____53777  in
            aux uu____53773 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____53787) ->
            let bs = FStar_List.rev out  in
            let uu____53840 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____53840 with
             | (bs1,t2) ->
                 let uu____53849 = patterns t2  in
                 (match uu____53849 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____53899 -> FStar_Pervasives_Native.None  in
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
      let uu____53991 = un_squash t  in
      FStar_Util.bind_opt uu____53991
        (fun t1  ->
           let uu____54007 = head_and_args' t1  in
           match uu____54007 with
           | (hd1,args) ->
               let uu____54046 =
                 let uu____54052 =
                   let uu____54053 = un_uinst hd1  in
                   uu____54053.FStar_Syntax_Syntax.n  in
                 (uu____54052, (FStar_List.length args))  in
               (match uu____54046 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_54069) when
                    (_54069 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_54072) when
                    (_54072 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_54075) when
                    (_54075 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_54078) when
                    (_54078 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_54081) when
                    (_54081 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_54084) when
                    (_54084 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_54087) when
                    (_54087 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_54090) when
                    (_54090 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____54091 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____54121 = un_squash t  in
      FStar_Util.bind_opt uu____54121
        (fun t1  ->
           let uu____54136 = arrow_one t1  in
           match uu____54136 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____54151 =
                 let uu____54153 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____54153  in
               if uu____54151
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____54163 = comp_to_comp_typ_nouniv c  in
                    uu____54163.FStar_Syntax_Syntax.result_typ  in
                  let uu____54164 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____54164
                  then
                    let uu____54171 = patterns q  in
                    match uu____54171 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____54234 =
                       let uu____54235 =
                         let uu____54240 =
                           let uu____54241 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____54252 =
                             let uu____54263 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____54263]  in
                           uu____54241 :: uu____54252  in
                         (FStar_Parser_Const.imp_lid, uu____54240)  in
                       BaseConn uu____54235  in
                     FStar_Pervasives_Native.Some uu____54234))
           | uu____54296 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____54304 = un_squash t  in
      FStar_Util.bind_opt uu____54304
        (fun t1  ->
           let uu____54335 = head_and_args' t1  in
           match uu____54335 with
           | (hd1,args) ->
               let uu____54374 =
                 let uu____54389 =
                   let uu____54390 = un_uinst hd1  in
                   uu____54390.FStar_Syntax_Syntax.n  in
                 (uu____54389, args)  in
               (match uu____54374 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____54407)::(a2,uu____54409)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____54460 =
                      let uu____54461 = FStar_Syntax_Subst.compress a2  in
                      uu____54461.FStar_Syntax_Syntax.n  in
                    (match uu____54460 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____54468) ->
                         let uu____54503 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____54503 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____54556 -> failwith "impossible"  in
                              let uu____54564 = patterns q1  in
                              (match uu____54564 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____54625 -> FStar_Pervasives_Native.None)
                | uu____54626 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____54649 = destruct_sq_forall phi  in
          (match uu____54649 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _54659  -> FStar_Pervasives_Native.Some _54659)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____54666 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____54672 = destruct_sq_exists phi  in
          (match uu____54672 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _54682  -> FStar_Pervasives_Native.Some _54682)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____54689 -> f1)
      | uu____54692 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____54696 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____54696
      (fun uu____54701  ->
         let uu____54702 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____54702
           (fun uu____54707  ->
              let uu____54708 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____54708
                (fun uu____54713  ->
                   let uu____54714 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____54714
                     (fun uu____54719  ->
                        let uu____54720 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____54720
                          (fun uu____54724  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____54737 =
      let uu____54738 = FStar_Syntax_Subst.compress t  in
      uu____54738.FStar_Syntax_Syntax.n  in
    match uu____54737 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____54745) ->
        let uu____54780 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____54780 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____54814 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____54814
             then
               let uu____54821 =
                 let uu____54832 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____54832]  in
               mk_app t uu____54821
             else e1)
    | uu____54859 ->
        let uu____54860 =
          let uu____54871 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____54871]  in
        mk_app t uu____54860
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____54913 =
            let uu____54918 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____54918  in
          let uu____54919 =
            let uu____54920 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____54920  in
          let uu____54923 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____54913 a.FStar_Syntax_Syntax.action_univs uu____54919
            FStar_Parser_Const.effect_Tot_lid uu____54923 [] pos
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
    let uu____54949 =
      let uu____54956 =
        let uu____54957 =
          let uu____54974 =
            let uu____54985 = FStar_Syntax_Syntax.as_arg t  in [uu____54985]
             in
          (reify_1, uu____54974)  in
        FStar_Syntax_Syntax.Tm_app uu____54957  in
      FStar_Syntax_Syntax.mk uu____54956  in
    uu____54949 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____55037 =
        let uu____55044 =
          let uu____55045 =
            let uu____55046 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____55046  in
          FStar_Syntax_Syntax.Tm_constant uu____55045  in
        FStar_Syntax_Syntax.mk uu____55044  in
      uu____55037 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____55048 =
      let uu____55055 =
        let uu____55056 =
          let uu____55073 =
            let uu____55084 = FStar_Syntax_Syntax.as_arg t  in [uu____55084]
             in
          (reflect_, uu____55073)  in
        FStar_Syntax_Syntax.Tm_app uu____55056  in
      FStar_Syntax_Syntax.mk uu____55055  in
    uu____55048 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____55128 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____55153 = unfold_lazy i  in delta_qualifier uu____55153
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____55155 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____55156 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____55157 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____55180 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____55193 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____55194 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____55201 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____55202 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____55218) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____55223;
           FStar_Syntax_Syntax.index = uu____55224;
           FStar_Syntax_Syntax.sort = t2;_},uu____55226)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____55235) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____55241,uu____55242) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____55284) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____55309,t2,uu____55311) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____55336,t2) -> delta_qualifier t2
  
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
    let uu____55375 = delta_qualifier t  in incr_delta_depth uu____55375
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____55383 =
      let uu____55384 = FStar_Syntax_Subst.compress t  in
      uu____55384.FStar_Syntax_Syntax.n  in
    match uu____55383 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____55389 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____55405 =
      let uu____55422 = unmeta e  in head_and_args uu____55422  in
    match uu____55405 with
    | (head1,args) ->
        let uu____55453 =
          let uu____55468 =
            let uu____55469 = un_uinst head1  in
            uu____55469.FStar_Syntax_Syntax.n  in
          (uu____55468, args)  in
        (match uu____55453 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____55487) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____55511::(hd1,uu____55513)::(tl1,uu____55515)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____55582 =
               let uu____55585 =
                 let uu____55588 = list_elements tl1  in
                 FStar_Util.must uu____55588  in
               hd1 :: uu____55585  in
             FStar_Pervasives_Native.Some uu____55582
         | uu____55597 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____55621 .
    ('Auu____55621 -> 'Auu____55621) ->
      'Auu____55621 Prims.list -> 'Auu____55621 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____55647 = f a  in [uu____55647]
      | x::xs -> let uu____55652 = apply_last f xs  in x :: uu____55652
  
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
          let uu____55707 =
            let uu____55714 =
              let uu____55715 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____55715  in
            FStar_Syntax_Syntax.mk uu____55714  in
          uu____55707 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____55729 =
            let uu____55734 =
              let uu____55735 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____55735
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____55734 args  in
          uu____55729 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____55749 =
            let uu____55754 =
              let uu____55755 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____55755
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____55754 args  in
          uu____55749 FStar_Pervasives_Native.None pos  in
        let uu____55756 =
          let uu____55757 =
            let uu____55758 = FStar_Syntax_Syntax.iarg typ  in [uu____55758]
             in
          nil uu____55757 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____55792 =
                 let uu____55793 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____55802 =
                   let uu____55813 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____55822 =
                     let uu____55833 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____55833]  in
                   uu____55813 :: uu____55822  in
                 uu____55793 :: uu____55802  in
               cons1 uu____55792 t.FStar_Syntax_Syntax.pos) l uu____55756
  
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
        | uu____55942 -> false
  
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
          | uu____56056 -> false
  
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
        | uu____56222 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____56260 = FStar_ST.op_Bang debug_term_eq  in
          if uu____56260
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
        let t11 = let uu____56482 = unmeta_safe t1  in canon_app uu____56482
           in
        let t21 = let uu____56488 = unmeta_safe t2  in canon_app uu____56488
           in
        let uu____56491 =
          let uu____56496 =
            let uu____56497 =
              let uu____56500 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____56500  in
            uu____56497.FStar_Syntax_Syntax.n  in
          let uu____56501 =
            let uu____56502 =
              let uu____56505 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____56505  in
            uu____56502.FStar_Syntax_Syntax.n  in
          (uu____56496, uu____56501)  in
        match uu____56491 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____56507,uu____56508) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____56517,FStar_Syntax_Syntax.Tm_uinst uu____56518) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____56527,uu____56528) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____56553,FStar_Syntax_Syntax.Tm_delayed uu____56554) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____56579,uu____56580) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____56609,FStar_Syntax_Syntax.Tm_ascribed uu____56610) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____56649 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____56649
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____56654 = FStar_Const.eq_const c1 c2  in
            check "const" uu____56654
        | (FStar_Syntax_Syntax.Tm_type
           uu____56657,FStar_Syntax_Syntax.Tm_type uu____56658) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____56716 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____56716) &&
              (let uu____56726 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____56726)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____56775 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____56775) &&
              (let uu____56785 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____56785)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____56803 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____56803)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____56860 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____56860) &&
              (let uu____56864 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____56864)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____56953 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____56953) &&
              (let uu____56957 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____56957)
        | (FStar_Syntax_Syntax.Tm_lazy uu____56974,uu____56975) ->
            let uu____56976 =
              let uu____56978 = unlazy t11  in
              term_eq_dbg dbg uu____56978 t21  in
            check "lazy_l" uu____56976
        | (uu____56980,FStar_Syntax_Syntax.Tm_lazy uu____56981) ->
            let uu____56982 =
              let uu____56984 = unlazy t21  in
              term_eq_dbg dbg t11 uu____56984  in
            check "lazy_r" uu____56982
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____57029 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____57029))
              &&
              (let uu____57033 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____57033)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____57037),FStar_Syntax_Syntax.Tm_uvar (u2,uu____57039)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____57097 =
               let uu____57099 = eq_quoteinfo qi1 qi2  in uu____57099 = Equal
                in
             check "tm_quoted qi" uu____57097) &&
              (let uu____57102 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____57102)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____57132 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____57132) &&
                   (let uu____57136 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____57136)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____57155 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____57155) &&
                    (let uu____57159 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____57159))
                   &&
                   (let uu____57163 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____57163)
             | uu____57166 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____57172) -> fail "unk"
        | (uu____57174,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____57176,uu____57177) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____57179,uu____57180) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____57182,uu____57183) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____57185,uu____57186) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____57188,uu____57189) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____57191,uu____57192) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____57212,uu____57213) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____57229,uu____57230) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____57238,uu____57239) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____57257,uu____57258) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____57282,uu____57283) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____57298,uu____57299) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____57313,uu____57314) ->
            fail "bottom"
        | (uu____57322,FStar_Syntax_Syntax.Tm_bvar uu____57323) ->
            fail "bottom"
        | (uu____57325,FStar_Syntax_Syntax.Tm_name uu____57326) ->
            fail "bottom"
        | (uu____57328,FStar_Syntax_Syntax.Tm_fvar uu____57329) ->
            fail "bottom"
        | (uu____57331,FStar_Syntax_Syntax.Tm_constant uu____57332) ->
            fail "bottom"
        | (uu____57334,FStar_Syntax_Syntax.Tm_type uu____57335) ->
            fail "bottom"
        | (uu____57337,FStar_Syntax_Syntax.Tm_abs uu____57338) ->
            fail "bottom"
        | (uu____57358,FStar_Syntax_Syntax.Tm_arrow uu____57359) ->
            fail "bottom"
        | (uu____57375,FStar_Syntax_Syntax.Tm_refine uu____57376) ->
            fail "bottom"
        | (uu____57384,FStar_Syntax_Syntax.Tm_app uu____57385) ->
            fail "bottom"
        | (uu____57403,FStar_Syntax_Syntax.Tm_match uu____57404) ->
            fail "bottom"
        | (uu____57428,FStar_Syntax_Syntax.Tm_let uu____57429) ->
            fail "bottom"
        | (uu____57444,FStar_Syntax_Syntax.Tm_uvar uu____57445) ->
            fail "bottom"
        | (uu____57459,FStar_Syntax_Syntax.Tm_meta uu____57460) ->
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
               let uu____57495 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____57495)
          (fun q1  ->
             fun q2  ->
               let uu____57507 =
                 let uu____57509 = eq_aqual q1 q2  in uu____57509 = Equal  in
               check "arg qual" uu____57507) a1 a2

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
               let uu____57534 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____57534)
          (fun q1  ->
             fun q2  ->
               let uu____57546 =
                 let uu____57548 = eq_aqual q1 q2  in uu____57548 = Equal  in
               check "binder qual" uu____57546) b1 b2

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
        ((let uu____57568 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____57568) &&
           (let uu____57572 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____57572))
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
    fun uu____57582  ->
      fun uu____57583  ->
        match (uu____57582, uu____57583) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____57710 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____57710) &&
               (let uu____57714 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____57714))
              &&
              (let uu____57718 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____57760 -> false  in
               check "branch when" uu____57718)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____57781 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____57781) &&
           (let uu____57790 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____57790))
          &&
          (let uu____57794 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____57794)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____57811 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____57811 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____57865 ->
        let uu____57888 =
          let uu____57890 = FStar_Syntax_Subst.compress t  in
          sizeof uu____57890  in
        (Prims.parse_int "1") + uu____57888
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____57893 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____57893
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____57897 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____57897
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____57906 = sizeof t1  in (FStar_List.length us) + uu____57906
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____57910) ->
        let uu____57935 = sizeof t1  in
        let uu____57937 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____57952  ->
                 match uu____57952 with
                 | (bv,uu____57962) ->
                     let uu____57967 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____57967) (Prims.parse_int "0") bs
           in
        uu____57935 + uu____57937
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____57996 = sizeof hd1  in
        let uu____57998 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____58013  ->
                 match uu____58013 with
                 | (arg,uu____58023) ->
                     let uu____58028 = sizeof arg  in acc + uu____58028)
            (Prims.parse_int "0") args
           in
        uu____57996 + uu____57998
    | uu____58031 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____58045 =
        let uu____58046 = un_uinst t  in uu____58046.FStar_Syntax_Syntax.n
         in
      match uu____58045 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____58051 -> false
  
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
        let uu____58100 = FStar_Options.set_options t s  in
        match uu____58100 with
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
          ((let uu____58117 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____58117 (fun a1  -> ()));
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
          let uu____58132 = FStar_Options.internal_pop ()  in
          if uu____58132
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
    | FStar_Syntax_Syntax.Tm_delayed uu____58164 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____58191 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____58206 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____58207 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____58208 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____58217) ->
        let uu____58242 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____58242 with
         | (bs1,t2) ->
             let uu____58251 =
               FStar_List.collect
                 (fun uu____58263  ->
                    match uu____58263 with
                    | (b,uu____58273) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____58278 = unbound_variables t2  in
             FStar_List.append uu____58251 uu____58278)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____58303 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____58303 with
         | (bs1,c1) ->
             let uu____58312 =
               FStar_List.collect
                 (fun uu____58324  ->
                    match uu____58324 with
                    | (b,uu____58334) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____58339 = unbound_variables_comp c1  in
             FStar_List.append uu____58312 uu____58339)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____58348 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____58348 with
         | (bs,t2) ->
             let uu____58371 =
               FStar_List.collect
                 (fun uu____58383  ->
                    match uu____58383 with
                    | (b1,uu____58393) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____58398 = unbound_variables t2  in
             FStar_List.append uu____58371 uu____58398)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____58427 =
          FStar_List.collect
            (fun uu____58441  ->
               match uu____58441 with
               | (x,uu____58453) -> unbound_variables x) args
           in
        let uu____58462 = unbound_variables t1  in
        FStar_List.append uu____58427 uu____58462
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____58503 = unbound_variables t1  in
        let uu____58506 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____58521 = FStar_Syntax_Subst.open_branch br  in
                  match uu____58521 with
                  | (p,wopt,t2) ->
                      let uu____58543 = unbound_variables t2  in
                      let uu____58546 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____58543 uu____58546))
           in
        FStar_List.append uu____58503 uu____58506
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____58560) ->
        let uu____58601 = unbound_variables t1  in
        let uu____58604 =
          let uu____58607 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____58638 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____58607 uu____58638  in
        FStar_List.append uu____58601 uu____58604
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____58679 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____58682 =
          let uu____58685 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____58688 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____58693 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____58695 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____58695 with
                 | (uu____58716,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____58685 uu____58688  in
        FStar_List.append uu____58679 uu____58682
    | FStar_Syntax_Syntax.Tm_let ((uu____58718,lbs),t1) ->
        let uu____58738 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____58738 with
         | (lbs1,t2) ->
             let uu____58753 = unbound_variables t2  in
             let uu____58756 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____58763 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____58766 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____58763 uu____58766) lbs1
                in
             FStar_List.append uu____58753 uu____58756)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____58783 = unbound_variables t1  in
        let uu____58786 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____58825  ->
                      match uu____58825 with
                      | (a,uu____58837) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____58846,uu____58847,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____58853,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____58859 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____58868 -> []
          | FStar_Syntax_Syntax.Meta_named uu____58869 -> []  in
        FStar_List.append uu____58783 uu____58786

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____58876) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____58886) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____58896 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____58899 =
          FStar_List.collect
            (fun uu____58913  ->
               match uu____58913 with
               | (a,uu____58925) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____58896 uu____58899

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
            let uu____59040 = head_and_args h  in
            (match uu____59040 with
             | (head1,args) ->
                 let uu____59101 =
                   let uu____59102 = FStar_Syntax_Subst.compress head1  in
                   uu____59102.FStar_Syntax_Syntax.n  in
                 (match uu____59101 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____59155 -> aux (h :: acc) t))
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
      let uu____59179 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____59179 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2985_59221 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2985_59221.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2985_59221.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2985_59221.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2985_59221.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  